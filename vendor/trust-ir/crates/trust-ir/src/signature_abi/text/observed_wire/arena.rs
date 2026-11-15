// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Flat syntax storage, never a typed ABI or an authority-bearing report.

use super::*;
use core::mem::size_of;

pub(super) enum Node {
    Atom(String),
    Text(String),
    List(Vec<usize>),
    Record(Vec<(String, usize)>),
}

pub(super) struct Arena {
    nodes: Vec<Node>,
}

impl Arena {
    pub(super) fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    pub(super) fn push<O: ExecutionObserver>(
        &mut self,
        node: Node,
        out: &mut Writer<'_, '_, O>,
    ) -> R<usize> {
        let result = out
            .reserve(&mut self.nodes, 1)
            .and_then(|()| out.admit(1, size_of::<Node>()));
        if let Err(error) = result {
            node.retire(out);
            return Err(error);
        }
        let index = self.nodes.len();
        self.nodes.push(node);
        Ok(index)
    }

    pub(super) fn node<'a, O: ExecutionObserver>(
        &'a self,
        index: usize,
        out: &mut Writer<'_, '_, O>,
    ) -> R<&'a Node> {
        out.poll()?;
        self.nodes
            .get(index)
            .ok_or(ObservedValueError::UnsupportedValue)
    }

    /// Drain each owned payload, including on a refused original session.
    /// The caller must check the latched original stop after retirement.
    pub(super) fn retire<O: ExecutionObserver>(mut self, out: &mut Writer<'_, '_, O>) {
        while !self.nodes.is_empty() {
            out.session.retirement_poll(out.site);
            if let Some(node) = self.nodes.pop() {
                node.retire(out);
            }
        }
        out.retire(self.nodes);
    }

    /// After `check::validate_signature`, the grammar has only exact ordered
    /// schema fields, typed enum strings, bool/none and unsigned number atoms.
    /// Re-emitting those nodes with minimal numbers and the original quoting
    /// therefore equals `encode(read_signature(parsed))`, without allocating
    /// a second typed ABI. It is not an unchecked alternative acceptance path:
    /// the orchestrator checks all typed fields and compares the complete text.
    pub(super) fn emit_canonical<O: ExecutionObserver>(
        &self,
        root: usize,
        out: &mut Writer<'_, '_, O>,
    ) -> R {
        self.emit(root, 0, out)
    }

    fn emit<O: ExecutionObserver>(
        &self,
        root: usize,
        depth: usize,
        out: &mut Writer<'_, '_, O>,
    ) -> R {
        if depth > MAX_DEPTH {
            return Err(ObservedValueError::UnsupportedValue);
        }
        match self.node(root, out)? {
            Node::Atom(value) => {
                if literal(value, "true", out)?
                    || literal(value, "false", out)?
                    || literal(value, "none", out)?
                {
                    out.append(value)
                } else {
                    let value = number(value, out)?;
                    out.number(value)
                }
            }
            Node::Text(value) => out.quoted(value),
            Node::List(values) => {
                out.append("[")?;
                for (index, value) in values.iter().enumerate() {
                    out.poll()?;
                    if index != 0 {
                        out.append(",")?;
                    }
                    self.emit(*value, depth + 1, out)?;
                }
                out.append("]")
            }
            Node::Record(fields) => {
                out.append("{")?;
                for (index, (key, value)) in fields.iter().enumerate() {
                    out.poll()?;
                    if index != 0 {
                        out.append(",")?;
                    }
                    out.append(key)?;
                    out.append("=")?;
                    self.emit(*value, depth + 1, out)?;
                }
                out.append("}")
            }
        }
    }
}

impl Node {
    pub(super) fn retire<O: ExecutionObserver>(self, out: &mut Writer<'_, '_, O>) {
        match self {
            Self::Atom(value) | Self::Text(value) => out.retire(value),
            // Child IDs own no subtree; the arena drains those nodes once.
            Self::List(values) => out.retire(values),
            Self::Record(mut fields) => {
                while !fields.is_empty() {
                    out.session.retirement_poll(out.site);
                    if let Some((key, _)) = fields.pop() {
                        out.retire(key);
                    }
                }
                out.retire(fields);
            }
        }
    }
}

pub(super) fn literal<O: ExecutionObserver>(
    value: &str,
    expected: &str,
    out: &mut Writer<'_, '_, O>,
) -> R<bool> {
    out.poll()?;
    if value.len() != expected.len() {
        return Ok(false);
    }
    // Call sites use fixed schema/enum tokens; equality never scans an
    // unchecked input-length word merely to decide its token class.
    out.admit(expected.len(), 0)?;
    Ok(value == expected)
}

pub(super) fn number<O: ExecutionObserver>(value: &str, out: &mut Writer<'_, '_, O>) -> R<u64> {
    out.poll()?;
    if value.is_empty() {
        return Err(ObservedValueError::UnsupportedValue);
    }
    let mut result = 0u64;
    for byte in value.bytes() {
        out.poll()?;
        if !byte.is_ascii_digit() {
            return Err(ObservedValueError::UnsupportedValue);
        }
        result = result
            .checked_mul(10)
            .and_then(|n| n.checked_add(u64::from(byte - b'0')))
            .ok_or(ObservedValueError::UnsupportedValue)?;
    }
    Ok(result)
}
