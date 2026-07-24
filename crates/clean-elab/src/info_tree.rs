// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Info tree infrastructure for IDE support.
//!
//! Info trees capture elaboration metadata (types, tactic goals, macro expansions)
//! alongside source spans. The LSP server queries these trees to provide hover
//! information, completions, and go-to-definition.
//!
//! # Architecture
//!
//! An `InfoTree` is a recursive tree whose internal nodes carry a source `Span`
//! plus an `InfoKind` describing the elaboration event, and whose leaves carry
//! concrete `InfoData` payloads consumable by IDE features.
//!
//! `InfoTreeBuilder` provides a stack-based construction API: `push_node` opens
//! a new scope, `add_leaf` attaches data, and `pop_node` closes the scope.
//! After elaboration, `build()` finalises the tree.
//!
//! `query_at_position` performs a depth-first search returning all `InfoData`
//! leaves whose enclosing node span contains the given byte offset.

use clean_kernel::{Expr, Name};
use clean_parser::{Span, SurfaceExpr};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A node in the info tree capturing elaboration metadata.
#[derive(Debug, Clone)]
pub(crate) struct InfoNode {
    /// Source span this node covers.
    pub(crate) span: Span,
    /// What kind of elaboration event this node represents.
    pub(crate) kind: InfoKind,
}

/// Classification of elaboration events recorded in the info tree.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum InfoKind {
    /// A term was elaborated, producing a kernel expression and its type.
    TermInfo { elaborated: Expr, type_: Expr },
    /// A tactic was applied, transforming the goal list.
    TacticInfo {
        goals_before: Vec<Expr>,
        goals_after: Vec<Expr>,
    },
    /// A field access on a structure.
    FieldInfo { struct_name: Name, field_name: Name },
    /// A top-level command was elaborated.
    CommandInfo { command_name: String },
    /// A macro was expanded.
    MacroExpansion {
        before: SurfaceExpr,
        after: SurfaceExpr,
    },
}

/// Leaf data in the info tree, directly consumed by IDE features.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum InfoData {
    /// Hover: show `expr : type`.
    TypeAscription(Expr, Expr),
    /// Completion context: prefix name and candidate completions.
    CompletionContext(Name, Vec<Name>),
    /// Go-to-definition hover: declaration name and its type.
    DefinitionHover(Name, Expr),
}

/// Recursive info tree produced during elaboration.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum InfoTree {
    /// An internal node with children.
    Node {
        node: InfoNode,
        children: Vec<InfoTree>,
    },
    /// A leaf carrying IDE-consumable data.
    Leaf(InfoData),
}

// ---------------------------------------------------------------------------
// Builder
// ---------------------------------------------------------------------------

/// Frame on the builder stack, accumulating children for one node.
struct BuilderFrame {
    node: InfoNode,
    children: Vec<InfoTree>,
}

/// Stack-based builder for constructing an `InfoTree` during elaboration.
///
/// Usage:
/// ```text
/// let mut builder = InfoTreeBuilder::new();
/// builder.push_node(span, InfoKind::TermInfo { .. });
///   builder.add_leaf(InfoData::TypeAscription(..));
/// builder.pop_node();
/// let tree = builder.build();
/// ```
#[must_use]
pub(crate) struct InfoTreeBuilder {
    /// Stack of open nodes. The last entry is the current scope.
    stack: Vec<BuilderFrame>,
    /// Top-level children accumulated before the first push or after the last pop.
    roots: Vec<InfoTree>,
}

impl InfoTreeBuilder {
    /// Create a new empty builder.
    pub(crate) fn new() -> Self {
        Self {
            stack: Vec::new(),
            roots: Vec::new(),
        }
    }

    /// Open a new node scope. All subsequent `add_leaf` / `push_node` calls
    /// become children of this node until the matching `pop_node`.
    pub(crate) fn push_node(&mut self, span: Span, kind: InfoKind) {
        self.stack.push(BuilderFrame {
            node: InfoNode { span, kind },
            children: Vec::new(),
        });
    }

    /// Close the current node scope, attaching it as a child of its parent
    /// (or as a root if no parent is open).
    ///
    /// # Panics
    ///
    /// Panics if no node is currently open (unbalanced push/pop).
    pub(crate) fn pop_node(&mut self) {
        let frame = self
            .stack
            .pop()
            .expect("invariant: pop_node called without matching push_node");
        let tree = InfoTree::Node {
            node: frame.node,
            children: frame.children,
        };
        // Attach to parent frame, or to roots if stack is now empty.
        if let Some(parent) = self.stack.last_mut() {
            parent.children.push(tree);
        } else {
            self.roots.push(tree);
        }
    }

    /// Add a leaf to the current node (or to the root list if no node is open).
    pub(crate) fn add_leaf(&mut self, data: InfoData) {
        let leaf = InfoTree::Leaf(data);
        if let Some(frame) = self.stack.last_mut() {
            frame.children.push(leaf);
        } else {
            self.roots.push(leaf);
        }
    }

    /// Finalise the builder, returning the constructed `InfoTree`.
    ///
    /// If multiple root-level entries exist they are wrapped in a synthetic
    /// root node with a dummy span. If exactly one root exists it is returned
    /// directly. An empty builder yields a `Leaf(TypeAscription)` with
    /// placeholder expressions (callers should treat a zero-child tree as
    /// empty).
    pub(crate) fn build(mut self) -> InfoTree {
        // Close any unclosed nodes (best-effort recovery).
        while !self.stack.is_empty() {
            self.pop_node();
        }

        match self.roots.len() {
            0 => InfoTree::Node {
                node: InfoNode {
                    span: Span::dummy(),
                    kind: InfoKind::CommandInfo {
                        command_name: String::new(),
                    },
                },
                children: Vec::new(),
            },
            1 => self.roots.pop().expect("invariant: len checked"),
            _ => InfoTree::Node {
                node: InfoNode {
                    span: Span::dummy(),
                    kind: InfoKind::CommandInfo {
                        command_name: String::new(),
                    },
                },
                children: self.roots,
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Query
// ---------------------------------------------------------------------------

/// Collect all `InfoData` leaves whose enclosing node span contains `pos`.
///
/// `pos` is a byte offset in the source text. A span contains `pos` when
/// `span.start <= pos && pos < span.end`.
///
/// Returns references in depth-first pre-order.
#[must_use]
pub(crate) fn query_at_position(tree: &InfoTree, pos: usize) -> Vec<&InfoData> {
    let mut results = Vec::new();
    query_recursive(tree, pos, true, &mut results);
    results
}

/// Recursive helper for `query_at_position`.
///
/// `in_scope` tracks whether the current position is within an ancestor's span.
/// Leaves are only collected when `in_scope` is true.
fn query_recursive<'a>(
    tree: &'a InfoTree,
    pos: usize,
    in_scope: bool,
    out: &mut Vec<&'a InfoData>,
) {
    match tree {
        InfoTree::Node { node, children } => {
            let contains = node.span.start <= pos && pos < node.span.end;
            // If this node's span contains pos, search children in-scope.
            // Also recurse into children when in_scope is already true and this
            // is a synthetic root (dummy span), so that top-level leaves are
            // reachable.
            let child_scope = contains || (in_scope && node.span == Span::dummy());
            for child in children {
                query_recursive(child, pos, child_scope, out);
            }
        }
        InfoTree::Leaf(data) => {
            if in_scope {
                out.push(data);
            }
        }
    }
}
