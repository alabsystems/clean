// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser for Mizar's `mizar-items` XML export format.
//!
//! Mizar's XML export is produced by the `mizar-items` tool and contains:
//! - Articles with definitions, theorems, schemes, registrations
//! - Formulas: `<For>`, `<Not>`, `<And>`, `<Pred>`, `<Is>`, etc.
//! - Terms: `<Var>`, `<Num>`, `<Func>`, `<Fraenkel>`, etc.
//! - Types: `<Typ>` with mode/struct/cluster info
//!
//! We parse using a lightweight approach: a minimal XML tokenizer that
//! extracts elements and attributes without a full XML DOM.

use super::types::{
    MizAdjective, MizArticle, MizDefinition, MizEnviron, MizFormula, MizItem, MizNotation,
    MizProof, MizProofStep, MizRegistration, MizScheme, MizTerm, MizTheorem, MizType,
};
use thiserror::Error;

/// Errors raised during Mizar XML parsing.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MizXmlError {
    #[error("unexpected end of input while parsing {context}")]
    UnexpectedEof { context: &'static str },
    #[error("expected element <{expected}>, found <{found}> at position {pos}")]
    UnexpectedElement {
        expected: String,
        found: String,
        pos: usize,
    },
    #[error("missing attribute `{attr}` on <{element}> at position {pos}")]
    MissingAttribute {
        attr: &'static str,
        element: String,
        pos: usize,
    },
    #[error("invalid integer `{value}` in attribute `{attr}` at position {pos}")]
    InvalidInteger {
        attr: &'static str,
        value: String,
        pos: usize,
    },
    #[error("unknown formula element <{tag}> at position {pos}")]
    UnknownFormulaTag { tag: String, pos: usize },
    #[error("unknown term element <{tag}> at position {pos}")]
    UnknownTermTag { tag: String, pos: usize },
    #[error("unknown item element <{tag}> at position {pos}")]
    UnknownItemTag { tag: String, pos: usize },
    #[error("malformed XML at position {pos}: {detail}")]
    MalformedXml { pos: usize, detail: String },
}

pub type MizXmlResult<T> = Result<T, MizXmlError>;

// ════════════════════════════════════════════════════════════════════════════
// Minimal XML tokenizer
// ════════════════════════════════════════════════════════════════════════════

/// A parsed XML element with attributes and child content.
#[derive(Debug, Clone)]
pub(crate) struct XmlElement {
    pub(crate) tag: String,
    pub(crate) attrs: Vec<(String, String)>,
    pub(crate) children: Vec<XmlElement>,
}

impl XmlElement {
    /// Get attribute value by name.
    pub(crate) fn attr(&self, name: &str) -> Option<&str> {
        self.attrs
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| v.as_str())
    }

    /// Get child elements.
    pub(crate) fn child_elements(&self) -> impl Iterator<Item = &XmlElement> {
        self.children.iter()
    }

    /// Find first child element with the given tag.
    pub(crate) fn find_child(&self, tag: &str) -> Option<&XmlElement> {
        self.child_elements().find(|e| e.tag == tag)
    }
}

/// Parse a complete XML document into a tree of elements.
///
/// This is a minimal parser sufficient for Mizar XML. It handles:
/// - Open/close tags with attributes
/// - Self-closing tags
/// - Text content
/// - XML declaration (`<?xml ... ?>`)
/// - Comments (`<!-- ... -->`)
pub(crate) fn parse_xml(input: &str) -> MizXmlResult<XmlElement> {
    let mut parser = XmlParser::new(input);
    parser.skip_prolog()?;
    parser.parse_element()
}

struct XmlParser<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> XmlParser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    fn remaining(&self) -> &'a str {
        &self.input[self.pos..]
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.input.len() && self.input.as_bytes()[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    fn skip_prolog(&mut self) -> MizXmlResult<()> {
        self.skip_whitespace();
        // Skip XML declaration
        if self.remaining().starts_with("<?") {
            if let Some(end) = self.remaining().find("?>") {
                self.pos += end + 2;
            }
        }
        self.skip_whitespace();
        // Skip DOCTYPE
        if self.remaining().starts_with("<!DOCTYPE") {
            if let Some(end) = self.remaining().find('>') {
                self.pos += end + 1;
            }
        }
        self.skip_whitespace();
        Ok(())
    }

    fn skip_comments(&mut self) {
        loop {
            self.skip_whitespace();
            if self.remaining().starts_with("<!--") {
                if let Some(end) = self.remaining().find("-->") {
                    self.pos += end + 3;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }

    fn parse_element(&mut self) -> MizXmlResult<XmlElement> {
        self.skip_comments();
        self.skip_whitespace();

        if !self.remaining().starts_with('<') {
            return Err(MizXmlError::MalformedXml {
                pos: self.pos,
                detail: "expected '<'".to_owned(),
            });
        }
        self.pos += 1; // skip '<'

        let tag = self.parse_name()?;
        let attrs = self.parse_attributes()?;

        self.skip_whitespace();

        // Self-closing tag?
        if self.remaining().starts_with("/>") {
            self.pos += 2;
            return Ok(XmlElement {
                tag,
                attrs,
                children: Vec::new(),
            });
        }

        // Expect '>'
        if !self.remaining().starts_with('>') {
            return Err(MizXmlError::MalformedXml {
                pos: self.pos,
                detail: format!("expected '>' or '/>' in tag <{tag}>"),
            });
        }
        self.pos += 1;

        // Parse children until closing tag
        let mut children = Vec::new();
        loop {
            self.skip_comments();
            self.skip_whitespace();

            if self.pos >= self.input.len() {
                return Err(MizXmlError::UnexpectedEof {
                    context: "element children",
                });
            }

            // Check for closing tag
            if self.remaining().starts_with("</") {
                self.pos += 2;
                let close_tag = self.parse_name()?;
                self.skip_whitespace();
                if !self.remaining().starts_with('>') {
                    return Err(MizXmlError::MalformedXml {
                        pos: self.pos,
                        detail: format!("expected '>' in closing tag </{close_tag}>"),
                    });
                }
                self.pos += 1;
                if close_tag != tag {
                    return Err(MizXmlError::MalformedXml {
                        pos: self.pos,
                        detail: format!("mismatched tags: <{tag}> closed by </{close_tag}>"),
                    });
                }
                break;
            }

            // Child element?
            if self.remaining().starts_with('<') {
                children.push(self.parse_element()?);
            } else {
                // Text content
                while self.pos < self.input.len() && self.input.as_bytes()[self.pos] != b'<' {
                    self.pos += 1;
                }
                // Mizar's item export stores semantic content in elements and
                // attributes. Inter-element text is formatting whitespace (or
                // otherwise non-semantic), so do not allocate nodes for it.
            }
        }

        Ok(XmlElement {
            tag,
            attrs,
            children,
        })
    }

    fn parse_name(&mut self) -> MizXmlResult<String> {
        let start = self.pos;
        while self.pos < self.input.len() {
            let b = self.input.as_bytes()[self.pos];
            if b.is_ascii_alphanumeric() || b == b'_' || b == b'-' || b == b':' || b == b'.' {
                self.pos += 1;
            } else {
                break;
            }
        }
        if self.pos == start {
            return Err(MizXmlError::MalformedXml {
                pos: self.pos,
                detail: "expected element/attribute name".to_owned(),
            });
        }
        Ok(self.input[start..self.pos].to_owned())
    }

    fn parse_attributes(&mut self) -> MizXmlResult<Vec<(String, String)>> {
        let mut attrs = Vec::new();
        loop {
            self.skip_whitespace();
            if self.pos >= self.input.len() {
                break;
            }
            let next = self.input.as_bytes()[self.pos];
            if next == b'>' || next == b'/' {
                break;
            }
            let name = self.parse_name()?;
            self.skip_whitespace();
            if !self.remaining().starts_with('=') {
                return Err(MizXmlError::MalformedXml {
                    pos: self.pos,
                    detail: format!("expected '=' after attribute name `{name}`"),
                });
            }
            self.pos += 1;
            self.skip_whitespace();
            let value = self.parse_quoted_value()?;
            attrs.push((name, value));
        }
        Ok(attrs)
    }

    fn parse_quoted_value(&mut self) -> MizXmlResult<String> {
        if self.pos >= self.input.len() {
            return Err(MizXmlError::UnexpectedEof {
                context: "attribute value",
            });
        }
        let quote = self.input.as_bytes()[self.pos];
        if quote != b'"' && quote != b'\'' {
            return Err(MizXmlError::MalformedXml {
                pos: self.pos,
                detail: "expected quote character for attribute value".to_owned(),
            });
        }
        self.pos += 1;
        let start = self.pos;
        while self.pos < self.input.len() && self.input.as_bytes()[self.pos] != quote {
            self.pos += 1;
        }
        if self.pos >= self.input.len() {
            return Err(MizXmlError::UnexpectedEof {
                context: "attribute value",
            });
        }
        let value = unescape_xml(&self.input[start..self.pos]);
        self.pos += 1; // skip closing quote
        Ok(value)
    }
}

/// Unescape basic XML entities.
fn unescape_xml(s: &str) -> String {
    s.replace("&amp;", "&")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
}

// ════════════════════════════════════════════════════════════════════════════
// Public API
// ════════════════════════════════════════════════════════════════════════════

/// Parse a Mizar XML article from a string.
pub fn parse_article(xml: &str) -> MizXmlResult<MizArticle> {
    let root = parse_xml(xml)?;
    parse_article_element(&root)
}

/// Parse a single Mizar formula from an XML string.
///
/// The XML should contain a single formula element at the root
/// (e.g., `<For>`, `<Not>`, `<And>`, `<Pred>`).
pub fn parse_formula_xml(xml: &str) -> MizXmlResult<MizFormula> {
    let root = parse_xml(xml)?;
    parse_formula(&root)
}

/// Parse a single Mizar term from an XML string.
pub fn parse_term_xml(xml: &str) -> MizXmlResult<MizTerm> {
    let root = parse_xml(xml)?;
    parse_term(&root)
}

/// Parse a single Mizar type from an XML string.
pub fn parse_type_xml(xml: &str) -> MizXmlResult<MizType> {
    let root = parse_xml(xml)?;
    parse_type(&root)
}

// ════════════════════════════════════════════════════════════════════════════
// Article parsing
// ════════════════════════════════════════════════════════════════════════════

fn parse_article_element(elem: &XmlElement) -> MizXmlResult<MizArticle> {
    let name = elem.attr("aid").unwrap_or("").to_owned();

    let environ = elem
        .find_child("Environ")
        .map(parse_environ)
        .unwrap_or_else(|| Ok(MizEnviron::default()))?;

    let mut items = Vec::new();
    for child in elem.child_elements() {
        match child.tag.as_str() {
            "Theorem" | "JustifiedTheorem" => {
                items.push(MizItem::Theorem(parse_theorem(child)?));
            }
            "Definition" | "DefinitionBlock" => {
                if let Some(def) = parse_definition_block(child)? {
                    items.push(MizItem::Definition(def));
                }
            }
            "Scheme" | "SchemeBlock" => {
                items.push(MizItem::Scheme(parse_scheme(child)?));
            }
            "Registration" | "RegistrationBlock" => {
                if let Some(reg) = parse_registration_block(child)? {
                    items.push(MizItem::Registration(reg));
                }
            }
            "Notation" | "NotationBlock" => {
                if let Some(not) = parse_notation_block(child)? {
                    items.push(MizItem::Notation(not));
                }
            }
            // Skip non-item elements (Environ, etc.)
            _ => {}
        }
    }

    Ok(MizArticle {
        name,
        environ,
        items,
    })
}

fn parse_environ(elem: &XmlElement) -> MizXmlResult<MizEnviron> {
    let mut env = MizEnviron::default();
    for child in elem.child_elements() {
        let list = collect_directive_names(child);
        match child.tag.as_str() {
            "Vocabularies" => env.vocabularies = list,
            "Notations" => env.notations = list,
            "Constructors" => env.constructors = list,
            "Registrations" => env.registrations = list,
            "Requirements" => env.requirements = list,
            "Definitions" => env.definitions = list,
            "Equalities" => env.equalities = list,
            "Expansions" => env.expansions = list,
            "Schemes" => env.schemes = list,
            "Theorems" => env.theorems = list,
            _ => {}
        }
    }
    Ok(env)
}

/// Collect names from directive children (e.g., `<Directive name="XBOOLE_0"/>`).
fn collect_directive_names(elem: &XmlElement) -> Vec<String> {
    elem.child_elements()
        .filter_map(|c| c.attr("name").map(ToOwned::to_owned))
        .collect()
}

// ════════════════════════════════════════════════════════════════════════════
// Formula parsing
// ════════════════════════════════════════════════════════════════════════════

pub(crate) fn parse_formula(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    match elem.tag.as_str() {
        "For" => parse_for(elem),
        "Ex" => parse_ex(elem),
        "Not" => parse_not(elem),
        "And" => parse_and(elem),
        "Or" => parse_or(elem),
        "Pred" => parse_pred(elem),
        "Is" => parse_is_formula(elem),
        "Implies" => parse_implies(elem),
        "Iff" => parse_iff(elem),
        "Contradiction" => Ok(MizFormula::Contradiction),
        "Thesis" => Ok(MizFormula::Thesis),
        // Handle negation wrapped as <Not><Pred.../></Not> etc.
        tag => Err(MizXmlError::UnknownFormulaTag {
            tag: tag.to_owned(),
            pos: 0,
        }),
    }
}

fn parse_for(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let var = elem.attr("vid").unwrap_or("x").to_owned();
    let children: Vec<&XmlElement> = elem.child_elements().collect();
    if children.len() < 2 {
        return Err(MizXmlError::MalformedXml {
            pos: 0,
            detail: "<For> requires a type and a formula child".to_owned(),
        });
    }
    let ty = parse_type(children[0])?;
    let body = parse_formula(children[1])?;
    Ok(MizFormula::ForAll {
        var,
        ty,
        body: Box::new(body),
    })
}

fn parse_ex(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let var = elem.attr("vid").unwrap_or("x").to_owned();
    let children: Vec<&XmlElement> = elem.child_elements().collect();
    if children.len() < 2 {
        return Err(MizXmlError::MalformedXml {
            pos: 0,
            detail: "<Ex> requires a type and a formula child".to_owned(),
        });
    }
    let ty = parse_type(children[0])?;
    let body = parse_formula(children[1])?;
    Ok(MizFormula::Exists {
        var,
        ty,
        body: Box::new(body),
    })
}

fn parse_not(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let child = elem
        .child_elements()
        .next()
        .ok_or(MizXmlError::MalformedXml {
            pos: 0,
            detail: "<Not> requires a formula child".to_owned(),
        })?;
    Ok(MizFormula::Not(Box::new(parse_formula(child)?)))
}

fn parse_and(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let conjuncts = elem
        .child_elements()
        .map(parse_formula)
        .collect::<MizXmlResult<Vec<_>>>()?;
    Ok(MizFormula::And(conjuncts))
}

fn parse_or(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let disjuncts = elem
        .child_elements()
        .map(parse_formula)
        .collect::<MizXmlResult<Vec<_>>>()?;
    Ok(MizFormula::Or(disjuncts))
}

fn parse_pred(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let name = elem.attr("kind").unwrap_or("").to_owned() + elem.attr("nr").unwrap_or("");
    let args = elem
        .child_elements()
        .map(parse_term)
        .collect::<MizXmlResult<Vec<_>>>()?;
    Ok(MizFormula::Pred { name, args })
}

fn parse_is_formula(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let children: Vec<&XmlElement> = elem.child_elements().collect();
    if children.len() < 2 {
        return Err(MizXmlError::MalformedXml {
            pos: 0,
            detail: "<Is> requires a term and a type child".to_owned(),
        });
    }
    let term = parse_term(children[0])?;
    let ty = parse_type(children[1])?;
    Ok(MizFormula::Is { term, ty })
}

fn parse_implies(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let children: Vec<&XmlElement> = elem.child_elements().collect();
    if children.len() < 2 {
        return Err(MizXmlError::MalformedXml {
            pos: 0,
            detail: "<Implies> requires two formula children".to_owned(),
        });
    }
    let lhs = parse_formula(children[0])?;
    let rhs = parse_formula(children[1])?;
    Ok(MizFormula::Implies(Box::new(lhs), Box::new(rhs)))
}

fn parse_iff(elem: &XmlElement) -> MizXmlResult<MizFormula> {
    let children: Vec<&XmlElement> = elem.child_elements().collect();
    if children.len() < 2 {
        return Err(MizXmlError::MalformedXml {
            pos: 0,
            detail: "<Iff> requires two formula children".to_owned(),
        });
    }
    let lhs = parse_formula(children[0])?;
    let rhs = parse_formula(children[1])?;
    Ok(MizFormula::Iff(Box::new(lhs), Box::new(rhs)))
}

// ════════════════════════════════════════════════════════════════════════════
// Term parsing
// ════════════════════════════════════════════════════════════════════════════

pub(crate) fn parse_term(elem: &XmlElement) -> MizXmlResult<MizTerm> {
    match elem.tag.as_str() {
        "Var" => {
            let nr = elem.attr("nr").unwrap_or("0");
            // Mizar XML uses numeric variable references; we name them xN.
            Ok(MizTerm::Var(format!("x{nr}")))
        }
        "Num" => {
            let nr = elem.attr("nr").unwrap_or("0");
            let value = nr.parse::<i64>().map_err(|_| MizXmlError::InvalidInteger {
                attr: "nr",
                value: nr.to_owned(),
                pos: 0,
            })?;
            Ok(MizTerm::Numeral(value))
        }
        "Func" => {
            let name = elem.attr("kind").unwrap_or("").to_owned() + elem.attr("nr").unwrap_or("");
            let args = elem
                .child_elements()
                .map(parse_term)
                .collect::<MizXmlResult<Vec<_>>>()?;
            Ok(MizTerm::Functor { name, args })
        }
        "Aggregate" => {
            let struct_name = elem.attr("nr").unwrap_or("").to_owned();
            let fields = elem
                .child_elements()
                .map(parse_term)
                .collect::<MizXmlResult<Vec<_>>>()?;
            Ok(MizTerm::Aggregate {
                struct_name,
                fields,
            })
        }
        "Selector" => {
            let field = elem.attr("nr").unwrap_or("").to_owned();
            let arg = elem
                .child_elements()
                .next()
                .ok_or(MizXmlError::MalformedXml {
                    pos: 0,
                    detail: "<Selector> requires a term child".to_owned(),
                })?;
            Ok(MizTerm::Selector {
                field,
                arg: Box::new(parse_term(arg)?),
            })
        }
        "The" => {
            let type_elem = elem
                .child_elements()
                .next()
                .ok_or(MizXmlError::MalformedXml {
                    pos: 0,
                    detail: "<The> requires a type child".to_owned(),
                })?;
            Ok(MizTerm::The {
                ty: parse_type(type_elem)?,
            })
        }
        "Fraenkel" => parse_fraenkel(elem),
        "It" => Ok(MizTerm::It),
        tag => Err(MizXmlError::UnknownTermTag {
            tag: tag.to_owned(),
            pos: 0,
        }),
    }
}

fn parse_fraenkel(elem: &XmlElement) -> MizXmlResult<MizTerm> {
    let children: Vec<&XmlElement> = elem.child_elements().collect();
    // Fraenkel: the last child is the formula, second-to-last is the term,
    // and preceding children are variable binders (Typ elements).
    if children.len() < 2 {
        return Err(MizXmlError::MalformedXml {
            pos: 0,
            detail: "<Fraenkel> requires at least a term and formula child".to_owned(),
        });
    }

    let formula_elem = children[children.len() - 1];
    let term_elem = children[children.len() - 2];

    let mut vars = Vec::new();
    for binder in &children[..children.len().saturating_sub(2)] {
        let var_name = binder.attr("vid").unwrap_or("x").to_owned();
        let ty = parse_type(binder)?;
        vars.push((var_name, ty));
    }

    let term = parse_term(term_elem)?;
    let formula = parse_formula(formula_elem)?;

    Ok(MizTerm::Fraenkel {
        term: Box::new(term),
        vars,
        formula: Box::new(formula),
    })
}

// ════════════════════════════════════════════════════════════════════════════
// Type parsing
// ════════════════════════════════════════════════════════════════════════════

pub(crate) fn parse_type(elem: &XmlElement) -> MizXmlResult<MizType> {
    match elem.tag.as_str() {
        "Typ" => parse_typ(elem),
        "Cluster" | "ClusteredType" => parse_clustered_type(elem),
        "Set" => Ok(MizType::Set),
        // If we get a tag we don't recognize, try treating it as a mode.
        tag => {
            // Check if it has a "kind" attribute indicating mode or struct.
            if let Some(kind) = elem.attr("kind") {
                match kind {
                    "G" => {
                        let name = elem.attr("nr").unwrap_or(tag).to_owned();
                        let args = elem
                            .child_elements()
                            .filter(|c| is_term_tag(&c.tag))
                            .map(parse_term)
                            .collect::<MizXmlResult<Vec<_>>>()?;
                        Ok(MizType::Struct { name, args })
                    }
                    _ => {
                        let name = elem.attr("nr").unwrap_or(tag).to_owned();
                        let args = elem
                            .child_elements()
                            .filter(|c| is_term_tag(&c.tag))
                            .map(parse_term)
                            .collect::<MizXmlResult<Vec<_>>>()?;
                        Ok(MizType::Mode { name, args })
                    }
                }
            } else {
                Ok(MizType::Mode {
                    name: tag.to_owned(),
                    args: Vec::new(),
                })
            }
        }
    }
}

fn parse_typ(elem: &XmlElement) -> MizXmlResult<MizType> {
    let kind = elem.attr("kind").unwrap_or("M");

    // Check for adjective clusters in children.
    let adjectives: Vec<MizAdjective> = elem
        .child_elements()
        .filter(|c| c.tag == "Adjective" || c.tag == "Cluster")
        .flat_map(|c| {
            if c.tag == "Cluster" {
                // A <Cluster> wraps multiple <Adjective> elements.
                c.child_elements()
                    .filter(|a| a.tag == "Adjective")
                    .map(parse_adjective)
                    .collect::<Vec<_>>()
            } else {
                vec![parse_adjective(c)]
            }
        })
        .collect::<MizXmlResult<Vec<_>>>()?;

    let term_args: Vec<MizTerm> = elem
        .child_elements()
        .filter(|c| is_term_tag(&c.tag))
        .map(parse_term)
        .collect::<MizXmlResult<Vec<_>>>()?;

    let name = elem.attr("nr").unwrap_or("").to_owned();

    let base = match kind {
        "G" => MizType::Struct {
            name,
            args: term_args,
        },
        "set" => MizType::Set,
        _ => MizType::Mode {
            name,
            args: term_args,
        },
    };

    if adjectives.is_empty() {
        Ok(base)
    } else {
        Ok(MizType::Clustered {
            adjectives,
            base: Box::new(base),
        })
    }
}

fn parse_clustered_type(elem: &XmlElement) -> MizXmlResult<MizType> {
    let adjectives = elem
        .child_elements()
        .filter(|c| c.tag == "Adjective")
        .map(parse_adjective)
        .collect::<MizXmlResult<Vec<_>>>()?;

    // The base type is the last non-Adjective child.
    let base_elem = elem
        .child_elements()
        .filter(|c| c.tag != "Adjective")
        .last()
        .ok_or(MizXmlError::MalformedXml {
            pos: 0,
            detail: "Clustered type requires a base type child".to_owned(),
        })?;

    let base = parse_type(base_elem)?;

    if adjectives.is_empty() {
        Ok(base)
    } else {
        Ok(MizType::Clustered {
            adjectives,
            base: Box::new(base),
        })
    }
}

fn parse_adjective(elem: &XmlElement) -> MizXmlResult<MizAdjective> {
    let name = elem.attr("nr").unwrap_or("").to_owned();
    let negated = elem.attr("value") == Some("false");
    let args = elem
        .child_elements()
        .filter(|c| is_term_tag(&c.tag))
        .map(parse_term)
        .collect::<MizXmlResult<Vec<_>>>()?;
    Ok(MizAdjective {
        name,
        negated,
        args,
    })
}

/// Check if a tag name represents a term element.
fn is_term_tag(tag: &str) -> bool {
    matches!(
        tag,
        "Var" | "Num" | "Func" | "Aggregate" | "Selector" | "The" | "Fraenkel" | "It"
    )
}

// ════════════════════════════════════════════════════════════════════════════
// Item parsing
// ════════════════════════════════════════════════════════════════════════════

fn parse_theorem(elem: &XmlElement) -> MizXmlResult<MizTheorem> {
    let label = elem.attr("nr").unwrap_or("").to_owned();

    let prop_elem = elem
        .child_elements()
        .find(|c| !matches!(c.tag.as_str(), "Proof" | "By" | "From"))
        .ok_or(MizXmlError::MalformedXml {
            pos: 0,
            detail: "Theorem requires a proposition child".to_owned(),
        })?;
    let proposition = parse_formula(prop_elem)?;

    let proof = elem.find_child("Proof").map(parse_proof).transpose()?;

    Ok(MizTheorem {
        label,
        proposition,
        proof,
    })
}

fn parse_definition_block(elem: &XmlElement) -> MizXmlResult<Option<MizDefinition>> {
    // Look for specific definition types inside the block.
    for child in elem.child_elements() {
        match child.tag.as_str() {
            "ModeDef" | "ModeDefinition" => {
                return Ok(Some(parse_mode_def(child)?));
            }
            "FuncDef" | "FunctorDefinition" => {
                return Ok(Some(parse_functor_def(child)?));
            }
            "PredDef" | "PredicateDefinition" => {
                return Ok(Some(parse_predicate_def(child)?));
            }
            "AttrDef" | "AttributeDefinition" => {
                return Ok(Some(parse_attribute_def(child)?));
            }
            "StructDef" | "StructureDefinition" => {
                return Ok(Some(parse_struct_def(child)?));
            }
            _ => {}
        }
    }
    // If the element itself is a definition type, try parsing it directly.
    match elem.tag.as_str() {
        "Definition" if elem.attr("kind").is_some() => match elem.attr("kind").unwrap_or("") {
            "M" => Ok(Some(parse_mode_def(elem)?)),
            "K" | "O" => Ok(Some(parse_functor_def(elem)?)),
            "R" | "V" => Ok(Some(parse_predicate_def(elem)?)),
            "G" => Ok(Some(parse_struct_def(elem)?)),
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn parse_mode_def(elem: &XmlElement) -> MizXmlResult<MizDefinition> {
    let name = elem.attr("nr").unwrap_or("").to_owned();
    let params = parse_binder_list(elem)?;
    let expansion = elem
        .child_elements()
        .find(|c| c.tag == "Typ" || c.tag == "Expansion")
        .map(|c| {
            if c.tag == "Expansion" {
                c.child_elements()
                    .next()
                    .map(parse_type)
                    .unwrap_or(Ok(MizType::Set))
            } else {
                parse_type(c)
            }
        })
        .transpose()?;
    Ok(MizDefinition::ModeDef {
        name,
        params,
        expansion,
    })
}

fn parse_functor_def(elem: &XmlElement) -> MizXmlResult<MizDefinition> {
    let name = elem.attr("nr").unwrap_or("").to_owned();
    let params = parse_binder_list(elem)?;
    let result_ty = elem
        .child_elements()
        .find(|c| c.tag == "Typ")
        .map(parse_type)
        .unwrap_or(Ok(MizType::Set))?;
    let value = elem
        .child_elements()
        .find(|c| is_term_tag(&c.tag) || c.tag == "Definiens")
        .map(|c| {
            if c.tag == "Definiens" {
                c.child_elements()
                    .find(|cc| is_term_tag(&cc.tag))
                    .map(parse_term)
                    .unwrap_or(Ok(MizTerm::It))
            } else {
                parse_term(c)
            }
        })
        .transpose()?;
    Ok(MizDefinition::FunctorDef {
        name,
        params,
        result_ty,
        value,
    })
}

fn parse_predicate_def(elem: &XmlElement) -> MizXmlResult<MizDefinition> {
    let name = elem.attr("nr").unwrap_or("").to_owned();
    let params = parse_binder_list(elem)?;
    let meaning = elem
        .child_elements()
        .find(|c| c.tag == "Definiens" || is_formula_tag(&c.tag))
        .map(|c| {
            if c.tag == "Definiens" {
                c.child_elements()
                    .find(|cc| is_formula_tag(&cc.tag))
                    .map(parse_formula)
                    .unwrap_or(Ok(MizFormula::Thesis))
            } else {
                parse_formula(c)
            }
        })
        .transpose()?;
    Ok(MizDefinition::PredicateDef {
        name,
        params,
        meaning,
    })
}

fn parse_attribute_def(elem: &XmlElement) -> MizXmlResult<MizDefinition> {
    let name = elem.attr("nr").unwrap_or("").to_owned();
    let params = parse_binder_list(elem)?;
    let meaning = elem
        .child_elements()
        .find(|c| c.tag == "Definiens" || is_formula_tag(&c.tag))
        .map(|c| {
            if c.tag == "Definiens" {
                c.child_elements()
                    .find(|cc| is_formula_tag(&cc.tag))
                    .map(parse_formula)
                    .unwrap_or(Ok(MizFormula::Thesis))
            } else {
                parse_formula(c)
            }
        })
        .transpose()?;
    Ok(MizDefinition::AttributeDef {
        name,
        params,
        meaning,
    })
}

fn parse_struct_def(elem: &XmlElement) -> MizXmlResult<MizDefinition> {
    let name = elem.attr("nr").unwrap_or("").to_owned();
    let ancestors: Vec<String> = elem
        .child_elements()
        .filter(|c| c.tag == "Ancestor" || c.tag == "Ancestors")
        .flat_map(|c| {
            if c.tag == "Ancestors" {
                c.child_elements()
                    .filter_map(|a| a.attr("nr").map(ToOwned::to_owned))
                    .collect::<Vec<_>>()
            } else {
                c.attr("nr").map(|s| vec![s.to_owned()]).unwrap_or_default()
            }
        })
        .collect();
    let fields = parse_binder_list(elem)?;
    Ok(MizDefinition::StructDef {
        name,
        ancestors,
        fields,
    })
}

fn parse_scheme(elem: &XmlElement) -> MizXmlResult<MizScheme> {
    let name = elem.attr("nr").unwrap_or("").to_owned();
    let mut premises = Vec::new();
    let mut conclusion = MizFormula::Thesis;

    for child in elem.child_elements() {
        match child.tag.as_str() {
            "SchemePremises" | "Premises" => {
                for p in child.child_elements() {
                    if is_formula_tag(&p.tag) {
                        premises.push(parse_formula(p)?);
                    }
                }
            }
            tag if is_formula_tag(tag) => {
                conclusion = parse_formula(child)?;
            }
            _ => {}
        }
    }

    Ok(MizScheme {
        name,
        premises,
        conclusion,
    })
}

fn parse_registration_block(elem: &XmlElement) -> MizXmlResult<Option<MizRegistration>> {
    for child in elem.child_elements() {
        match child.tag.as_str() {
            "ExistentialRegistration" | "RCluster" => {
                return Ok(Some(parse_existential_reg(child)?));
            }
            "ConditionalRegistration" | "CCluster" => {
                return Ok(Some(parse_conditional_reg(child)?));
            }
            "FunctorialRegistration" | "FCluster" => {
                return Ok(Some(parse_functorial_reg(child)?));
            }
            _ => {}
        }
    }
    Ok(None)
}

fn parse_existential_reg(elem: &XmlElement) -> MizXmlResult<MizRegistration> {
    let adjectives = parse_adjective_list(elem)?;
    let ty = elem
        .child_elements()
        .find(|c| c.tag == "Typ")
        .map(parse_type)
        .unwrap_or(Ok(MizType::Set))?;
    Ok(MizRegistration::Existential { adjectives, ty })
}

fn parse_conditional_reg(elem: &XmlElement) -> MizXmlResult<MizRegistration> {
    let mut clusters: Vec<Vec<MizAdjective>> = Vec::new();
    for child in elem.child_elements() {
        if child.tag == "Cluster" || child.tag == "Adjective" {
            clusters.push(if child.tag == "Cluster" {
                child
                    .child_elements()
                    .filter(|c| c.tag == "Adjective")
                    .map(parse_adjective)
                    .collect::<MizXmlResult<Vec<_>>>()?
            } else {
                vec![parse_adjective(child)?]
            });
        }
    }
    let (antecedent, consequent) = if clusters.len() >= 2 {
        (clusters[0].clone(), clusters[1].clone())
    } else {
        (Vec::new(), clusters.into_iter().flatten().collect())
    };
    let ty = elem
        .child_elements()
        .find(|c| c.tag == "Typ")
        .map(parse_type)
        .unwrap_or(Ok(MizType::Set))?;
    Ok(MizRegistration::Conditional {
        antecedent,
        consequent,
        ty,
    })
}

fn parse_functorial_reg(elem: &XmlElement) -> MizXmlResult<MizRegistration> {
    let term = elem
        .child_elements()
        .find(|c| is_term_tag(&c.tag))
        .map(parse_term)
        .unwrap_or(Ok(MizTerm::It))?;
    let adjectives = parse_adjective_list(elem)?;
    Ok(MizRegistration::Functorial { term, adjectives })
}

fn parse_notation_block(elem: &XmlElement) -> MizXmlResult<Option<MizNotation>> {
    for child in elem.child_elements() {
        match child.tag.as_str() {
            "Synonym" => {
                let new_name = child.attr("nr").unwrap_or("").to_owned();
                let original = child.attr("origin").unwrap_or("").to_owned();
                return Ok(Some(MizNotation::Synonym { new_name, original }));
            }
            "Antonym" => {
                let new_name = child.attr("nr").unwrap_or("").to_owned();
                let original = child.attr("origin").unwrap_or("").to_owned();
                return Ok(Some(MizNotation::Antonym { new_name, original }));
            }
            _ => {}
        }
    }
    Ok(None)
}

// ════════════════════════════════════════════════════════════════════════════
// Proof parsing
// ════════════════════════════════════════════════════════════════════════════

fn parse_proof(elem: &XmlElement) -> MizXmlResult<MizProof> {
    let steps = elem
        .child_elements()
        .filter_map(|c| parse_proof_step(c).transpose())
        .collect::<MizXmlResult<Vec<_>>>()?;
    Ok(MizProof { steps })
}

fn parse_proof_step(elem: &XmlElement) -> MizXmlResult<Option<MizProofStep>> {
    match elem.tag.as_str() {
        "Let" => {
            let var = elem.attr("vid").unwrap_or("x").to_owned();
            let ty = elem
                .child_elements()
                .next()
                .map(parse_type)
                .unwrap_or(Ok(MizType::Set))?;
            Ok(Some(MizProofStep::Let { var, ty }))
        }
        "Assume" => {
            let formula = elem
                .child_elements()
                .next()
                .map(parse_formula)
                .unwrap_or(Ok(MizFormula::Thesis))?;
            Ok(Some(MizProofStep::Assume(formula)))
        }
        "Thus" | "Hence" => {
            let formula = elem
                .child_elements()
                .next()
                .map(parse_formula)
                .unwrap_or(Ok(MizFormula::Thesis))?;
            Ok(Some(MizProofStep::Thus(formula)))
        }
        "Consider" => {
            let var = elem.attr("vid").unwrap_or("x").to_owned();
            let children: Vec<&XmlElement> = elem.child_elements().collect();
            let ty = children
                .first()
                .map(|c| parse_type(c))
                .unwrap_or(Ok(MizType::Set))?;
            let condition = children
                .get(1)
                .map(|c| parse_formula(c))
                .unwrap_or(Ok(MizFormula::Thesis))?;
            Ok(Some(MizProofStep::Consider { var, ty, condition }))
        }
        "Take" => {
            let term = elem
                .child_elements()
                .next()
                .map(parse_term)
                .unwrap_or(Ok(MizTerm::It))?;
            Ok(Some(MizProofStep::Take(term)))
        }
        "Set" => {
            let var = elem.attr("vid").unwrap_or("x").to_owned();
            let value = elem
                .child_elements()
                .find(|c| is_term_tag(&c.tag))
                .map(parse_term)
                .unwrap_or(Ok(MizTerm::It))?;
            Ok(Some(MizProofStep::Set { var, value }))
        }
        "Reconsider" => {
            let var = elem.attr("vid").unwrap_or("x").to_owned();
            let ty = elem
                .child_elements()
                .find(|c| c.tag == "Typ")
                .map(parse_type)
                .unwrap_or(Ok(MizType::Set))?;
            Ok(Some(MizProofStep::Reconsider { var, ty }))
        }
        "Proof" => Ok(Some(MizProofStep::SubProof(parse_proof(elem)?))),
        "By" | "From" => {
            let refs = elem
                .child_elements()
                .filter_map(|c| c.attr("nr").map(ToOwned::to_owned))
                .collect();
            Ok(Some(MizProofStep::ByRef(refs)))
        }
        "Hereby" => {
            let steps = elem
                .child_elements()
                .filter_map(|c| parse_proof_step(c).transpose())
                .collect::<MizXmlResult<Vec<_>>>()?;
            Ok(Some(MizProofStep::Hereby(steps)))
        }
        "PerCases" | "CaseBlock" => {
            let cases = parse_per_cases(elem)?;
            Ok(Some(MizProofStep::PerCases { cases }))
        }
        // Skip unknown proof elements silently.
        _ => Ok(None),
    }
}

fn parse_per_cases(elem: &XmlElement) -> MizXmlResult<Vec<(MizFormula, Vec<MizProofStep>)>> {
    let mut cases = Vec::new();
    for child in elem.child_elements() {
        if child.tag == "Case" || child.tag == "CaseBlock" {
            let formula = child
                .child_elements()
                .find(|c| is_formula_tag(&c.tag))
                .map(parse_formula)
                .unwrap_or(Ok(MizFormula::Thesis))?;
            let steps = child
                .child_elements()
                .filter(|c| !is_formula_tag(&c.tag))
                .filter_map(|c| parse_proof_step(c).transpose())
                .collect::<MizXmlResult<Vec<_>>>()?;
            cases.push((formula, steps));
        }
    }
    Ok(cases)
}

// ════════════════════════════════════════════════════════════════════════════
// Helpers
// ════════════════════════════════════════════════════════════════════════════

fn parse_binder_list(elem: &XmlElement) -> MizXmlResult<Vec<(String, MizType)>> {
    let mut params = Vec::new();
    for child in elem.child_elements() {
        if child.tag == "Typ" || child.tag == "ArgTypes" {
            if child.tag == "ArgTypes" {
                for arg in child.child_elements() {
                    let var_name = arg.attr("vid").unwrap_or("x").to_owned();
                    let ty = parse_type(arg)?;
                    params.push((var_name, ty));
                }
            } else {
                let var_name = child.attr("vid").unwrap_or("x").to_owned();
                let ty = parse_type(child)?;
                params.push((var_name, ty));
            }
        }
    }
    Ok(params)
}

fn parse_adjective_list(elem: &XmlElement) -> MizXmlResult<Vec<MizAdjective>> {
    elem.child_elements()
        .filter(|c| c.tag == "Adjective" || c.tag == "Cluster")
        .flat_map(|c| {
            if c.tag == "Cluster" {
                c.child_elements()
                    .filter(|a| a.tag == "Adjective")
                    .map(parse_adjective)
                    .collect::<Vec<_>>()
            } else {
                vec![parse_adjective(c)]
            }
        })
        .collect()
}

/// Check if a tag name represents a formula element.
fn is_formula_tag(tag: &str) -> bool {
    matches!(
        tag,
        "For"
            | "Ex"
            | "Not"
            | "And"
            | "Or"
            | "Pred"
            | "Is"
            | "Implies"
            | "Iff"
            | "Contradiction"
            | "Thesis"
    )
}

// ════════════════════════════════════════════════════════════════════════════
// Complete article parsing (with error recovery)
// ════════════════════════════════════════════════════════════════════════════

/// Diagnostic message collected during error-recovering article parse.
#[derive(Debug, Clone)]
pub struct MizParseDiagnostic {
    /// Position (byte offset) in the XML where the issue occurred.
    pub pos: usize,
    /// Human-readable description.
    pub message: String,
    /// The XML tag that triggered the diagnostic (if known).
    pub tag: Option<String>,
}

/// Result of parsing a Mizar article with error recovery.
#[derive(Debug, Clone)]
pub struct MizArticleParseResult {
    /// The parsed article (may be partial if errors occurred).
    pub article: MizArticle,
    /// Diagnostics collected during parsing (warnings, skipped elements).
    pub diagnostics: Vec<MizParseDiagnostic>,
    /// Number of items successfully parsed.
    pub items_parsed: usize,
    /// Number of items skipped due to parse errors.
    pub items_skipped: usize,
}

impl MizArticleParseResult {
    /// Whether parsing completed without any skipped items.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.items_skipped == 0
    }

    /// Whether any items were successfully parsed.
    #[must_use]
    pub fn has_items(&self) -> bool {
        self.items_parsed > 0
    }
}

/// Parse a complete Mizar article XML with error recovery.
///
/// Unlike [`parse_article`], this function attempts to continue parsing
/// when individual items contain malformed XML. Malformed items are
/// skipped and recorded in the diagnostics list.
///
/// This is the preferred entry point for batch import pipelines where
/// partial results are better than total failure.
pub fn parse_mizar_article(xml: &str) -> MizXmlResult<MizArticleParseResult> {
    let root = parse_xml(xml)?;
    parse_article_with_recovery(&root)
}

/// Parse an article element with per-item error recovery.
fn parse_article_with_recovery(elem: &XmlElement) -> MizXmlResult<MizArticleParseResult> {
    let name = elem.attr("aid").unwrap_or("").to_owned();

    let environ = elem
        .find_child("Environ")
        .map(parse_environ)
        .unwrap_or_else(|| Ok(MizEnviron::default()))?;

    let mut items = Vec::new();
    let mut diagnostics = Vec::new();
    let mut items_parsed = 0usize;
    let mut items_skipped = 0usize;

    for child in elem.child_elements() {
        let result = match child.tag.as_str() {
            "Theorem" | "JustifiedTheorem" => {
                parse_theorem(child).map(|t| Some(MizItem::Theorem(t)))
            }
            "Definition" | "DefinitionBlock" => {
                parse_definition_block(child).map(|d| d.map(MizItem::Definition))
            }
            "Scheme" | "SchemeBlock" => parse_scheme(child).map(|s| Some(MizItem::Scheme(s))),
            "Registration" | "RegistrationBlock" => {
                parse_registration_block(child).map(|r| r.map(MizItem::Registration))
            }
            "Notation" | "NotationBlock" => {
                parse_notation_block(child).map(|n| n.map(MizItem::Notation))
            }
            _ => continue,
        };

        match result {
            Ok(Some(item)) => {
                items.push(item);
                items_parsed += 1;
            }
            Ok(None) => {
                // Item was recognized but empty (e.g., notation block with no declarations).
                items_skipped += 1;
                diagnostics.push(MizParseDiagnostic {
                    pos: 0,
                    message: format!("empty {} block skipped", child.tag),
                    tag: Some(child.tag.clone()),
                });
            }
            Err(e) => {
                items_skipped += 1;
                diagnostics.push(MizParseDiagnostic {
                    pos: 0,
                    message: format!("skipped malformed <{}>: {e}", child.tag),
                    tag: Some(child.tag.clone()),
                });
            }
        }
    }

    Ok(MizArticleParseResult {
        article: MizArticle {
            name,
            environ,
            items,
        },
        diagnostics,
        items_parsed,
        items_skipped,
    })
}

// ════════════════════════════════════════════════════════════════════════════
// Enhanced registration parsing
// ════════════════════════════════════════════════════════════════════════════

/// Parse all registrations from a `<RegistrationBlock>` or article element.
///
/// Returns all registrations found in the element (not just the first one,
/// as `parse_registration_block` does).
pub(crate) fn parse_registrations(elem: &XmlElement) -> MizXmlResult<Vec<MizRegistration>> {
    let mut regs = Vec::new();
    for child in elem.child_elements() {
        match child.tag.as_str() {
            "ExistentialRegistration" | "RCluster" => {
                regs.push(parse_existential_reg(child)?);
            }
            "ConditionalRegistration" | "CCluster" => {
                regs.push(parse_conditional_reg(child)?);
            }
            "FunctorialRegistration" | "FCluster" => {
                regs.push(parse_functorial_reg(child)?);
            }
            "Registration" | "RegistrationBlock" => {
                // Recurse into nested registration blocks.
                regs.extend(parse_registrations(child)?);
            }
            _ => {}
        }
    }
    Ok(regs)
}

/// Parse all registrations from an article XML string.
///
/// Scans the full article for all registration blocks and returns
/// every registration found.
pub fn parse_registrations_from_xml(xml: &str) -> MizXmlResult<Vec<MizRegistration>> {
    let root = parse_xml(xml)?;
    parse_registrations(&root)
}

// ════════════════════════════════════════════════════════════════════════════
// Enhanced notation parsing
// ════════════════════════════════════════════════════════════════════════════

/// Parse all notations from a `<NotationBlock>` or article element.
///
/// Returns all notation declarations found in the element.
pub(crate) fn parse_notations(elem: &XmlElement) -> MizXmlResult<Vec<MizNotation>> {
    let mut notes = Vec::new();
    for child in elem.child_elements() {
        match child.tag.as_str() {
            "Synonym" => {
                let new_name = child.attr("nr").unwrap_or("").to_owned();
                let original = child.attr("origin").unwrap_or("").to_owned();
                notes.push(MizNotation::Synonym { new_name, original });
            }
            "Antonym" => {
                let new_name = child.attr("nr").unwrap_or("").to_owned();
                let original = child.attr("origin").unwrap_or("").to_owned();
                notes.push(MizNotation::Antonym { new_name, original });
            }
            "Notation" | "NotationBlock" => {
                // Recurse into nested notation blocks.
                notes.extend(parse_notations(child)?);
            }
            _ => {}
        }
    }
    Ok(notes)
}

/// Parse all notations from an article XML string.
pub fn parse_notations_from_xml(xml: &str) -> MizXmlResult<Vec<MizNotation>> {
    let root = parse_xml(xml)?;
    parse_notations(&root)
}

// ════════════════════════════════════════════════════════════════════════════
// Scheme parsing enhancements
// ════════════════════════════════════════════════════════════════════════════

/// Parse all schemes from an article XML string.
pub fn parse_schemes_from_xml(xml: &str) -> MizXmlResult<Vec<MizScheme>> {
    let root = parse_xml(xml)?;
    parse_all_schemes(&root)
}

/// Extract all schemes from an article element.
fn parse_all_schemes(elem: &XmlElement) -> MizXmlResult<Vec<MizScheme>> {
    let mut schemes = Vec::new();
    for child in elem.child_elements() {
        match child.tag.as_str() {
            "Scheme" | "SchemeBlock" => {
                schemes.push(parse_scheme(child)?);
            }
            _ => {}
        }
    }
    Ok(schemes)
}

// ════════════════════════════════════════════════════════════════════════════
// Article environment extraction
// ════════════════════════════════════════════════════════════════════════════

/// Extract just the environment block from an article XML, without
/// parsing the full item list.
///
/// Useful for dependency resolution before full import.
pub fn parse_environ_only(xml: &str) -> MizXmlResult<MizEnviron> {
    let root = parse_xml(xml)?;
    root.find_child("Environ")
        .map(parse_environ)
        .unwrap_or_else(|| Ok(MizEnviron::default()))
}

// ════════════════════════════════════════════════════════════════════════════
// Validation helpers
// ════════════════════════════════════════════════════════════════════════════

/// Check if an XML string appears to be a valid Mizar article
/// (has an `<Article>` root element with an `aid` attribute).
///
/// This is a lightweight check that does not parse the full document.
#[must_use]
pub fn is_mizar_article_xml(xml: &str) -> bool {
    let trimmed = xml.trim();
    // Skip XML declaration if present.
    let content = if trimmed.starts_with("<?xml") {
        match trimmed.find("?>") {
            Some(end) => trimmed[end + 2..].trim_start(),
            None => return false,
        }
    } else {
        trimmed
    };
    // Check for <Article with aid attribute.
    content.starts_with("<Article") && content.contains("aid=")
}

/// Count the approximate number of items in an article XML without
/// fully parsing the tree.
///
/// Counts occurrences of item-level start tags. Fast but approximate;
/// use full parsing for exact counts.
#[must_use]
pub fn count_article_items_approx(xml: &str) -> usize {
    let item_tags = [
        "<Theorem",
        "<JustifiedTheorem",
        "<Definition ",
        "<DefinitionBlock",
        "<Scheme ",
        "<SchemeBlock",
        "<Registration ",
        "<RegistrationBlock",
        "<Notation ",
        "<NotationBlock",
    ];
    item_tags.iter().map(|tag| xml.matches(tag).count()).sum()
}

// ════════════════════════════════════════════════════════════════════════════
// Article structure analysis
// ════════════════════════════════════════════════════════════════════════════

/// Summary statistics from a parsed Mizar article XML.
#[derive(Debug, Clone, Default)]
pub struct MizArticleStats {
    /// Article name (from `aid` attribute).
    pub name: String,
    /// Number of theorem items.
    pub theorems: usize,
    /// Number of definition blocks.
    pub definitions: usize,
    /// Number of scheme blocks.
    pub schemes: usize,
    /// Number of registration blocks.
    pub registrations: usize,
    /// Number of notation blocks.
    pub notations: usize,
    /// Number of environment dependencies.
    pub environ_deps: usize,
    /// Whether parsing encountered any errors.
    pub has_errors: bool,
}

impl MizArticleStats {
    /// Total item count.
    #[must_use]
    pub fn total_items(&self) -> usize {
        self.theorems + self.definitions + self.schemes + self.registrations + self.notations
    }
}

/// Quickly extract article statistics without building full AST items.
///
/// Faster than full parsing when only counts are needed (e.g., for triage).
pub fn article_stats(xml: &str) -> MizXmlResult<MizArticleStats> {
    let root = parse_xml(xml)?;
    let name = root.attr("aid").unwrap_or("").to_owned();

    let environ_deps = root
        .find_child("Environ")
        .map(|env| {
            env.child_elements()
                .map(|dir| dir.child_elements().count())
                .sum::<usize>()
        })
        .unwrap_or(0);

    let mut stats = MizArticleStats {
        name,
        environ_deps,
        ..MizArticleStats::default()
    };

    for child in root.child_elements() {
        match child.tag.as_str() {
            "Theorem" | "JustifiedTheorem" => stats.theorems += 1,
            "Definition" | "DefinitionBlock" => stats.definitions += 1,
            "Scheme" | "SchemeBlock" => stats.schemes += 1,
            "Registration" | "RegistrationBlock" => stats.registrations += 1,
            "Notation" | "NotationBlock" => stats.notations += 1,
            _ => {}
        }
    }

    Ok(stats)
}
