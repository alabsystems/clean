// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser for Isabelle's `.yxml` export format.
//!
//! YXML is an XML-like format using special byte delimiters instead of `<` and `>`:
//! - `\x05` (ENQ) replaces `<` — starts markup
//! - `\x06` (ACK) replaces `>` — ends markup / separates tag from attributes
//!
//! An element looks like: `\x05\x06name\x06key=value\x06...\x05` for an open tag,
//! and `\x05\x06\x05` for a close tag. Text between markup is preserved verbatim.
//!
//! Reference: Isabelle/Pure, `General/yxml.ML`
//! URL: https://isabelle.in.tum.de/repos/isabelle/file/tip/src/Pure/General/yxml.ML

use super::types::{IsaTerm, IsaTheorem, IsaTheoryExport, IsaType, ProofStatus};

/// YXML special delimiters.
const YXML_OPEN: u8 = 0x05; // ENQ — start of markup
const YXML_SEP: u8 = 0x06; // ACK — separator between tag/attrs and end of markup

/// Parsed YXML tree node.
///
/// An XML-like tree structure produced by parsing the YXML byte stream.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum YxmlTree {
    /// An element with tag name, attributes, and children.
    Element {
        name: String,
        attrs: Vec<(String, String)>,
        children: Vec<YxmlTree>,
    },
    /// A text node.
    Text(String),
}

impl YxmlTree {
    /// Get the tag name if this is an element.
    #[must_use]
    pub fn tag_name(&self) -> Option<&str> {
        match self {
            Self::Element { name, .. } => Some(name.as_str()),
            Self::Text(_) => None,
        }
    }

    /// Get an attribute value by key.
    #[must_use]
    pub fn attr(&self, key: &str) -> Option<&str> {
        match self {
            Self::Element { attrs, .. } => attrs
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v.as_str()),
            Self::Text(_) => None,
        }
    }

    /// Get children if this is an element.
    #[must_use]
    pub fn children(&self) -> &[YxmlTree] {
        match self {
            Self::Element { children, .. } => children.as_slice(),
            Self::Text(_) => &[],
        }
    }

    /// Get the text content of a text node, or concatenated text of children.
    #[must_use]
    pub fn text_content(&self) -> String {
        match self {
            Self::Text(s) => s.clone(),
            Self::Element { children, .. } => children.iter().map(|c| c.text_content()).collect(),
        }
    }

    /// Find the first child element with the given tag name.
    #[must_use]
    pub fn find_child(&self, tag: &str) -> Option<&YxmlTree> {
        self.children().iter().find(|c| c.tag_name() == Some(tag))
    }

    /// Find all child elements with the given tag name.
    #[must_use]
    pub fn find_children(&self, tag: &str) -> Vec<&YxmlTree> {
        self.children()
            .iter()
            .filter(|c| c.tag_name() == Some(tag))
            .collect()
    }
}

/// Errors that can occur during YXML parsing.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum YxmlError {
    #[error("unexpected end of input at byte offset {offset}")]
    UnexpectedEof { offset: usize },

    #[error("unmatched close tag at byte offset {offset}")]
    UnmatchedClose { offset: usize },

    #[error("malformed markup at byte offset {offset}: {detail}")]
    MalformedMarkup { offset: usize, detail: String },

    #[error("invalid UTF-8 in text at byte offset {offset}")]
    InvalidUtf8 { offset: usize },

    #[error("expected element <{expected}>, found <{found}>")]
    UnexpectedElement { expected: String, found: String },

    #[error("missing attribute '{attr}' on element <{element}>")]
    MissingAttribute { element: String, attr: String },

    #[error("invalid integer '{value}' for attribute '{attr}': {source}")]
    InvalidInt {
        attr: String,
        value: String,
        source: std::num::ParseIntError,
    },

    #[error("unknown term/type constructor: {name}")]
    UnknownConstructor { name: String },

    #[error("missing child element <{child}> in <{parent}>")]
    MissingChild { parent: String, child: String },
}

/// Result type for YXML operations.
pub type Result<T> = std::result::Result<T, YxmlError>;

/// Parse a YXML byte stream into a list of tree nodes.
///
/// The top level may contain multiple elements and/or text nodes.
/// Returns the parsed forest (list of trees).
///
/// # Errors
/// Returns `YxmlError` on malformed YXML input.
#[must_use = "parsing result should be checked"]
pub fn parse_yxml(input: &[u8]) -> Result<Vec<YxmlTree>> {
    let mut parser = YxmlParser::new(input);
    parser.parse_forest()
}

/// Parse YXML input and wrap results in a single root element.
///
/// If the input produces exactly one element, returns it directly.
/// Otherwise wraps multiple top-level nodes in a synthetic `<root>` element.
///
/// # Errors
/// Returns `YxmlError` on malformed YXML input.
pub fn parse_yxml_tree(input: &[u8]) -> Result<YxmlTree> {
    let mut nodes = parse_yxml(input)?;
    if nodes.len() == 1 {
        Ok(nodes.remove(0))
    } else {
        Ok(YxmlTree::Element {
            name: "root".to_owned(),
            attrs: Vec::new(),
            children: nodes,
        })
    }
}

/// Internal YXML parser state.
struct YxmlParser<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> YxmlParser<'a> {
    fn new(input: &'a [u8]) -> Self {
        Self { input, pos: 0 }
    }

    /// Parse a forest of top-level nodes.
    fn parse_forest(&mut self) -> Result<Vec<YxmlTree>> {
        let mut nodes = Vec::new();
        while self.pos < self.input.len() {
            if self.peek() == Some(YXML_OPEN) {
                // Check if this is a close tag
                if self.is_close_tag() {
                    // Close tag at top level means we've finished
                    break;
                }
                nodes.push(self.parse_element()?);
            } else {
                let text = self.parse_text()?;
                if !text.is_empty() {
                    nodes.push(YxmlTree::Text(text));
                }
            }
        }
        Ok(nodes)
    }

    /// Check if current position is a close tag: `\x05\x06\x05`
    fn is_close_tag(&self) -> bool {
        self.pos + 2 < self.input.len()
            && self.input[self.pos] == YXML_OPEN
            && self.input[self.pos + 1] == YXML_SEP
            && self.input[self.pos + 2] == YXML_OPEN
    }

    /// Parse an element: open tag, children, close tag.
    fn parse_element(&mut self) -> Result<YxmlTree> {
        let (name, attrs) = self.parse_open_tag()?;
        let mut children = Vec::new();

        loop {
            if self.pos >= self.input.len() {
                return Err(YxmlError::UnexpectedEof { offset: self.pos });
            }

            if self.is_close_tag() {
                // Consume the close tag: \x05\x06\x05
                self.pos += 3;
                break;
            }

            if self.peek() == Some(YXML_OPEN) {
                children.push(self.parse_element()?);
            } else {
                let text = self.parse_text()?;
                if !text.is_empty() {
                    children.push(YxmlTree::Text(text));
                }
            }
        }

        Ok(YxmlTree::Element {
            name,
            attrs,
            children,
        })
    }

    /// Parse an open tag: `\x05\x06name\x06key=value\x06...\x05`
    ///
    /// Format:
    /// - Starts with `\x05\x06`
    /// - Tag name terminated by `\x06` or `\x05`
    /// - Attributes: `key=value` separated by `\x06`
    /// - Ends with `\x05`
    fn parse_open_tag(&mut self) -> Result<(String, Vec<(String, String)>)> {
        let start = self.pos;

        // Expect \x05
        self.expect_byte(YXML_OPEN)?;
        // Expect \x06
        self.expect_byte(YXML_SEP)?;

        // Read tag name — up to next \x06 or \x05
        let name = self.read_until_any(&[YXML_SEP, YXML_OPEN])?;
        if name.is_empty() {
            return Err(YxmlError::MalformedMarkup {
                offset: start,
                detail: "empty tag name".to_owned(),
            });
        }

        let mut attrs = Vec::new();

        // Parse attributes separated by \x06 until we see \x05
        loop {
            match self.peek() {
                Some(YXML_OPEN) => {
                    // End of open tag
                    self.pos += 1;
                    break;
                }
                Some(YXML_SEP) => {
                    // Separator before next attribute
                    self.pos += 1;
                    // Read attribute: key=value
                    let attr_str = self.read_until_any(&[YXML_SEP, YXML_OPEN])?;
                    if !attr_str.is_empty() {
                        if let Some((key, value)) = attr_str.split_once('=') {
                            attrs.push((key.to_owned(), value.to_owned()));
                        } else {
                            // Attribute without value — treat as key=""
                            attrs.push((attr_str, String::new()));
                        }
                    }
                }
                Some(_) => {
                    return Err(YxmlError::MalformedMarkup {
                        offset: self.pos,
                        detail: format!(
                            "expected \\x05 or \\x06, found 0x{:02x}",
                            self.input[self.pos]
                        ),
                    });
                }
                None => {
                    return Err(YxmlError::UnexpectedEof { offset: self.pos });
                }
            }
        }

        Ok((name, attrs))
    }

    /// Parse text content until the next `\x05` or end of input.
    fn parse_text(&mut self) -> Result<String> {
        let start = self.pos;
        while self.pos < self.input.len() && self.input[self.pos] != YXML_OPEN {
            self.pos += 1;
        }
        let bytes = &self.input[start..self.pos];
        std::str::from_utf8(bytes)
            .map(|s| s.to_owned())
            .map_err(|_| YxmlError::InvalidUtf8 { offset: start })
    }

    /// Read a UTF-8 string until one of the stop bytes is encountered.
    fn read_until_any(&mut self, stops: &[u8]) -> Result<String> {
        let start = self.pos;
        while self.pos < self.input.len() && !stops.contains(&self.input[self.pos]) {
            self.pos += 1;
        }
        let bytes = &self.input[start..self.pos];
        std::str::from_utf8(bytes)
            .map(|s| s.to_owned())
            .map_err(|_| YxmlError::InvalidUtf8 { offset: start })
    }

    /// Expect and consume a specific byte.
    fn expect_byte(&mut self, expected: u8) -> Result<()> {
        if self.pos >= self.input.len() {
            return Err(YxmlError::UnexpectedEof { offset: self.pos });
        }
        if self.input[self.pos] != expected {
            return Err(YxmlError::MalformedMarkup {
                offset: self.pos,
                detail: format!(
                    "expected 0x{expected:02x}, found 0x{:02x}",
                    self.input[self.pos]
                ),
            });
        }
        self.pos += 1;
        Ok(())
    }

    /// Peek at the current byte without consuming.
    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos).copied()
    }
}

// ---------------------------------------------------------------------------
// Isabelle term/type tree interpretation
// ---------------------------------------------------------------------------

/// Helper to get a required attribute from a YXML element.
fn require_attr<'a>(tree: &'a YxmlTree, attr: &str) -> Result<&'a str> {
    tree.attr(attr).ok_or_else(|| YxmlError::MissingAttribute {
        element: tree.tag_name().unwrap_or("<text>").to_owned(),
        attr: attr.to_owned(),
    })
}

/// Helper to get a required child element.
fn require_child<'a>(tree: &'a YxmlTree, child_tag: &str) -> Result<&'a YxmlTree> {
    tree.find_child(child_tag)
        .ok_or_else(|| YxmlError::MissingChild {
            parent: tree.tag_name().unwrap_or("<text>").to_owned(),
            child: child_tag.to_owned(),
        })
}

/// Parse an Isabelle type from a YXML tree.
///
/// Isabelle encodes types in YXML as:
/// - `<TFree name="..." sort="..."/>` — free type variable
/// - `<TVar name="..." index="..." sort="..."/>` — schematic type variable
/// - `<Type name="...">child_types...</Type>` — type constructor
///
/// # Errors
/// Returns `YxmlError` if the tree does not represent a valid type.
pub fn parse_type(tree: &YxmlTree) -> Result<IsaType> {
    let tag = tree
        .tag_name()
        .ok_or_else(|| YxmlError::UnknownConstructor {
            name: "text node (expected type element)".to_owned(),
        })?;

    match tag {
        "TFree" => {
            let name = require_attr(tree, "name")?.to_owned();
            let sort = parse_sort(tree);
            Ok(IsaType::TFree { name, sort })
        }
        "TVar" => {
            let name = require_attr(tree, "name")?.to_owned();
            let index = parse_index_attr(tree, "index")?;
            let sort = parse_sort(tree);
            Ok(IsaType::TVar { name, index, sort })
        }
        "Type" => {
            let name = require_attr(tree, "name")?.to_owned();
            let args = tree
                .children()
                .iter()
                .filter(|c| c.tag_name().is_some())
                .map(parse_type)
                .collect::<Result<Vec<_>>>()?;
            Ok(IsaType::Type { name, args })
        }
        other => Err(YxmlError::UnknownConstructor {
            name: format!("type constructor: {other}"),
        }),
    }
}

/// Parse sort constraints from a tree's child elements or `sort` attribute.
fn parse_sort(tree: &YxmlTree) -> Vec<String> {
    // Try attribute first (compact encoding)
    if let Some(sort_str) = tree.attr("sort") {
        if sort_str.is_empty() {
            return Vec::new();
        }
        return sort_str.split(',').map(|s| s.trim().to_owned()).collect();
    }
    // Fall back to child <class> elements
    tree.find_children("class")
        .iter()
        .filter_map(|c| c.attr("name").map(|s| s.to_owned()))
        .collect()
}

/// Parse a `u32` attribute value.
fn parse_index_attr(tree: &YxmlTree, attr: &str) -> Result<u32> {
    let val_str = require_attr(tree, attr)?;
    val_str.parse::<u32>().map_err(|e| YxmlError::InvalidInt {
        attr: attr.to_owned(),
        value: val_str.to_owned(),
        source: e,
    })
}

/// Parse an Isabelle term from a YXML tree.
///
/// Isabelle encodes terms in YXML as:
/// - `<Bound index="N"/>` — de Bruijn index
/// - `<Free name="..."><type/></Free>` — free variable
/// - `<Var name="..." index="N"><type/></Var>` — schematic variable
/// - `<Const name="..."><type/></Const>` — named constant
/// - `<Abs name="..."><type/><body/></Abs>` — lambda abstraction
/// - `<App><fun/><arg/></App>` — application (also encoded as `$`)
///
/// # Errors
/// Returns `YxmlError` if the tree does not represent a valid term.
pub fn parse_term(tree: &YxmlTree) -> Result<IsaTerm> {
    let tag = tree
        .tag_name()
        .ok_or_else(|| YxmlError::UnknownConstructor {
            name: "text node (expected term element)".to_owned(),
        })?;

    match tag {
        "Bound" => {
            let index = parse_index_attr(tree, "index")?;
            Ok(IsaTerm::Bound(index))
        }
        "Free" => {
            let name = require_attr(tree, "name")?.to_owned();
            let ty = parse_first_type_child(tree, "Free")?;
            Ok(IsaTerm::Free { name, ty })
        }
        "Var" => {
            let name = require_attr(tree, "name")?.to_owned();
            let index = parse_index_attr(tree, "index")?;
            let ty = parse_first_type_child(tree, "Var")?;
            Ok(IsaTerm::Var { name, index, ty })
        }
        "Const" => {
            let name = require_attr(tree, "name")?.to_owned();
            let ty = parse_first_type_child(tree, "Const")?;
            Ok(IsaTerm::Const { name, ty })
        }
        "Abs" => {
            let name = require_attr(tree, "name")?.to_owned();
            let elem_children: Vec<&YxmlTree> = tree
                .children()
                .iter()
                .filter(|c| c.tag_name().is_some())
                .collect();

            if elem_children.len() < 2 {
                return Err(YxmlError::MissingChild {
                    parent: "Abs".to_owned(),
                    child: "type and body".to_owned(),
                });
            }
            let ty = parse_type(elem_children[0])?;
            let body = parse_term(elem_children[1])?;
            Ok(IsaTerm::Abs {
                name,
                ty,
                body: Box::new(body),
            })
        }
        "App" | "$" => {
            let elem_children: Vec<&YxmlTree> = tree
                .children()
                .iter()
                .filter(|c| c.tag_name().is_some())
                .collect();

            if elem_children.len() < 2 {
                return Err(YxmlError::MissingChild {
                    parent: tag.to_owned(),
                    child: "fun and arg".to_owned(),
                });
            }
            let fun = parse_term(elem_children[0])?;
            let arg = parse_term(elem_children[1])?;
            Ok(IsaTerm::App {
                fun: Box::new(fun),
                arg: Box::new(arg),
            })
        }
        other => Err(YxmlError::UnknownConstructor {
            name: format!("term constructor: {other}"),
        }),
    }
}

/// Parse the first type-like child element from a term node.
fn parse_first_type_child(tree: &YxmlTree, parent_tag: &str) -> Result<IsaType> {
    tree.children()
        .iter()
        .find(|c| matches!(c.tag_name(), Some("TFree") | Some("TVar") | Some("Type")))
        .map(parse_type)
        .unwrap_or_else(|| {
            Err(YxmlError::MissingChild {
                parent: parent_tag.to_owned(),
                child: "type (TFree|TVar|Type)".to_owned(),
            })
        })
}

/// Parse an Isabelle theorem from a YXML tree.
///
/// Expected structure:
/// ```xml
/// <theorem name="...">
///   <proof status="proved|axiomatized"/>
///   <prop>term...</prop>
///   ...
/// </theorem>
/// ```
///
/// # Errors
/// Returns `YxmlError` if the tree does not represent a valid theorem.
pub fn parse_theorem(tree: &YxmlTree) -> Result<IsaTheorem> {
    let tag = tree
        .tag_name()
        .ok_or_else(|| YxmlError::UnexpectedElement {
            expected: "theorem".to_owned(),
            found: "text".to_owned(),
        })?;

    if tag != "theorem" {
        return Err(YxmlError::UnexpectedElement {
            expected: "theorem".to_owned(),
            found: tag.to_owned(),
        });
    }

    let name = require_attr(tree, "name")?.to_owned();

    // Parse proof status
    let proof_status = if let Some(proof_elem) = tree.find_child("proof") {
        match proof_elem.attr("status") {
            Some("proved") => ProofStatus::Proved,
            Some("axiomatized") => ProofStatus::Axiomatized,
            _ => ProofStatus::Axiomatized, // default to axiomatized for unknown
        }
    } else {
        // No explicit proof element — default to axiomatized (conservative)
        ProofStatus::Axiomatized
    };

    // Parse propositions
    let props = tree
        .find_children("prop")
        .iter()
        .map(|prop_elem| {
            // The term is the first element child of <prop>
            prop_elem
                .children()
                .iter()
                .find(|c| c.tag_name().is_some())
                .map(parse_term)
                .unwrap_or_else(|| {
                    Err(YxmlError::MissingChild {
                        parent: "prop".to_owned(),
                        child: "term".to_owned(),
                    })
                })
        })
        .collect::<Result<Vec<_>>>()?;

    Ok(IsaTheorem {
        name,
        props,
        proof_status,
    })
}

/// Parse a complete Isabelle theory export from YXML bytes.
///
/// Expected top-level structure:
/// ```xml
/// <theory name="...">
///   <imports><dep name="..."/>...</imports>
///   <types><type_decl name="..."><Type .../></type_decl>...</types>
///   <consts><const_decl name="..."><Type .../></const_decl>...</consts>
///   <theorems><theorem ...>...</theorem>...</theorems>
/// </theory>
/// ```
///
/// # Errors
/// Returns `YxmlError` on parse failure.
pub fn parse_theory_export(input: &[u8]) -> Result<IsaTheoryExport> {
    let tree = parse_yxml_tree(input)?;

    // Find the theory element (might be the root, or wrapped)
    let theory = find_theory_element(&tree)?;

    let theory_name = require_attr(theory, "name")?.to_owned();

    // Parse dependencies from <imports>
    let dependencies = if let Some(imports) = theory.find_child("imports") {
        imports
            .find_children("dep")
            .iter()
            .filter_map(|dep| dep.attr("name").map(|s| s.to_owned()))
            .collect()
    } else {
        Vec::new()
    };

    // Parse type declarations from <types>
    let types = if let Some(types_elem) = theory.find_child("types") {
        types_elem
            .find_children("type_decl")
            .iter()
            .map(|td| {
                let name = require_attr(td, "name")?.to_owned();
                let ty = td
                    .children()
                    .iter()
                    .find(|c| c.tag_name().is_some())
                    .map(parse_type)
                    .unwrap_or_else(|| Ok(IsaType::nullary(&name)))?;
                Ok((name, ty))
            })
            .collect::<Result<Vec<_>>>()?
    } else {
        Vec::new()
    };

    // Parse constant declarations from <consts>
    let consts = if let Some(consts_elem) = theory.find_child("consts") {
        consts_elem
            .find_children("const_decl")
            .iter()
            .map(|cd| {
                let name = require_attr(cd, "name")?.to_owned();
                let ty = parse_first_type_child(cd, "const_decl")?;
                Ok((name, ty))
            })
            .collect::<Result<Vec<_>>>()?
    } else {
        Vec::new()
    };

    // Parse theorems from <theorems>
    let theorems = if let Some(thms_elem) = theory.find_child("theorems") {
        thms_elem
            .find_children("theorem")
            .iter()
            .map(|t| parse_theorem(t))
            .collect::<Result<Vec<_>>>()?
    } else {
        Vec::new()
    };

    Ok(IsaTheoryExport {
        theory_name,
        types,
        consts,
        theorems,
        dependencies,
    })
}

/// Find the `<theory>` element in a parsed tree.
fn find_theory_element(tree: &YxmlTree) -> Result<&YxmlTree> {
    if tree.tag_name() == Some("theory") {
        return Ok(tree);
    }
    // Search children
    if let Some(child) = tree.find_child("theory") {
        return Ok(child);
    }
    Err(YxmlError::UnexpectedElement {
        expected: "theory".to_owned(),
        found: tree.tag_name().unwrap_or("text").to_owned(),
    })
}

// ---------------------------------------------------------------------------
// YXML construction helpers (for testing)
// ---------------------------------------------------------------------------

/// Build a YXML open tag: `\x05\x06name\x06key=value...\x05`
#[cfg(test)]
pub(crate) fn yxml_open(name: &str, attrs: &[(&str, &str)]) -> Vec<u8> {
    let mut out = vec![YXML_OPEN, YXML_SEP];
    out.extend_from_slice(name.as_bytes());
    for (k, v) in attrs {
        out.push(YXML_SEP);
        out.extend_from_slice(k.as_bytes());
        out.push(b'=');
        out.extend_from_slice(v.as_bytes());
    }
    out.push(YXML_OPEN);
    out
}

/// Build a YXML close tag: `\x05\x06\x05`
#[cfg(test)]
pub(crate) fn yxml_close() -> Vec<u8> {
    vec![YXML_OPEN, YXML_SEP, YXML_OPEN]
}

/// Build a complete YXML element with text content.
#[cfg(test)]
pub(crate) fn yxml_elem(name: &str, attrs: &[(&str, &str)], content: &[u8]) -> Vec<u8> {
    let mut out = yxml_open(name, attrs);
    out.extend_from_slice(content);
    out.extend_from_slice(&yxml_close());
    out
}

/// Build a self-contained YXML element (open + close, no content).
#[cfg(test)]
pub(crate) fn yxml_leaf(name: &str, attrs: &[(&str, &str)]) -> Vec<u8> {
    let mut out = yxml_open(name, attrs);
    out.extend_from_slice(&yxml_close());
    out
}
