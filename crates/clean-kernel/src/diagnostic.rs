// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded, sharing-aware diagnostics. This is a lossy presentation of an
//! unchanged expression/error, never serialization or checking evidence.
//!
//! `Debug` and `Display` on the original types retain their existing behavior.
//! Use `format!("{}", error.diagnostic())` for untrusted or large proof DAGs.
//! Each rendering visits at most 128 expression/universe nodes, follows at most
//! 32 edges per path, and emits at most 8192 UTF-8 bytes. Names, strings, lists
//! and metadata have separate constant-size previews; no recursive formatter,
//! structural equality, hashing walk or complete payload conversion is called.

use crate::expr::{BigNat, Expr, ExprKind, Literal, ZFCSetExpr};
use crate::level::Level;
use crate::name::{Name, NameInner};
use crate::tc::TypeError;
use std::collections::HashMap;
use std::fmt::{self, Write};

/// Maximum UTF-8 bytes emitted by one bounded diagnostic, including omissions.
pub const MAX_DIAGNOSTIC_BYTES: usize = 8192;
/// Maximum distinct expression/universe allocations described in one rendering.
pub const MAX_DIAGNOSTIC_NODES: usize = 128;
/// Maximum number of expression/universe edges followed from either root.
pub const MAX_DIAGNOSTIC_DEPTH: usize = 32;
const FOOTER_RESERVE: usize = 96;
const TEXT_PREVIEW_BYTES: usize = 64;
const LIST_PREVIEW_ITEMS: usize = 8;

enum Root<'a> {
    Expr(&'a Expr),
    Error(&'a TypeError),
}

/// Borrowed diagnostic wrapper. Node IDs describe sharing within this one
/// rendering only; neither IDs nor omitted/previewed data are semantic hashes.
pub struct BoundedDiagnostic<'a>(Root<'a>);

impl Expr {
    /// A bounded DAG diagnostic, without expanding shared descendants again.
    pub fn diagnostic(&self) -> BoundedDiagnostic<'_> {
        BoundedDiagnostic(Root::Expr(self))
    }
}

impl TypeError {
    /// A bounded diagnostic preserving the error variant and field roles.
    /// The original error, expected/inferred terms and checker verdict remain
    /// untouched. Truncation is always labelled and grants no proof authority.
    pub fn diagnostic(&self) -> BoundedDiagnostic<'_> {
        BoundedDiagnostic(Root::Error(self))
    }
}

impl fmt::Display for BoundedDiagnostic<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&render(&self.0))
    }
}
impl fmt::Debug for BoundedDiagnostic<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[derive(Clone, Copy)]
enum Node<'a> {
    Expr(&'a Expr),
    Level(&'a Level),
}
impl Node<'_> {
    fn key(self) -> (u8, *const ()) {
        match self {
            Self::Expr(e) => (0, std::ptr::from_ref(e).cast()),
            Self::Level(l) => (1, std::ptr::from_ref(l).cast()),
        }
    }
}

struct Text {
    value: String,
    full: bool,
}
impl Text {
    fn new() -> Self {
        Self {
            value: String::with_capacity(MAX_DIAGNOSTIC_BYTES),
            full: false,
        }
    }
}
impl Write for Text {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        if self.full {
            return Err(fmt::Error);
        }
        let remaining = (MAX_DIAGNOSTIC_BYTES - FOOTER_RESERVE) - self.value.len();
        let mut end = remaining.min(text.len());
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        self.value.push_str(&text[..end]);
        if end < text.len() {
            self.full = true;
            return Err(fmt::Error);
        }
        Ok(())
    }
}

struct Renderer<'a> {
    text: Text,
    nodes: Vec<(Node<'a>, usize)>,
    ids: HashMap<(u8, *const ()), usize>,
    node_limit: bool,
    depth_limit: bool,
    preview: bool,
}

impl<'a> Renderer<'a> {
    fn new() -> Self {
        Self {
            text: Text::new(),
            nodes: Vec::with_capacity(MAX_DIAGNOSTIC_NODES),
            ids: HashMap::with_capacity(MAX_DIAGNOSTIC_NODES),
            node_limit: false,
            depth_limit: false,
            preview: false,
        }
    }
    fn reference(&mut self, node: Node<'a>, depth: usize) -> fmt::Result {
        if let Some(id) = self.ids.get(&node.key()) {
            return write!(self.text, "#{id}");
        }
        if depth > MAX_DIAGNOSTIC_DEPTH {
            self.depth_limit = true;
            return self.text.write_str("<depth-limit>");
        }
        if self.nodes.len() == MAX_DIAGNOSTIC_NODES {
            self.node_limit = true;
            return self.text.write_str("<node-limit>");
        }
        let id = self.nodes.len();
        self.ids.insert(node.key(), id);
        self.nodes.push((node, depth));
        write!(self.text, "#{id}")
    }
    fn expr(&mut self, expr: &'a Expr, depth: usize) -> fmt::Result {
        self.reference(Node::Expr(expr), depth)
    }
    fn text_preview(&mut self, text: &str) -> fmt::Result {
        let mut end = text.len().min(TEXT_PREVIEW_BYTES);
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        write!(self.text, "{:?}", &text[..end])?;
        if end < text.len() {
            self.preview = true;
            write!(self.text, "<text-preview; bytes={}>", text.len())?;
        }
        Ok(())
    }
    fn name(&mut self, name: &Name) -> fmt::Result {
        // Walking only the last three components also bounds work on a name
        // whose prefix itself contains millions of components.
        let mut parts = Vec::with_capacity(3);
        let mut current = name;
        for _ in 0..3 {
            match current.inner() {
                NameInner::Anon => break,
                NameInner::Str(parent, value) => {
                    parts.push((Some(value.as_ref()), 0));
                    current = parent;
                }
                NameInner::Num(parent, value) => {
                    parts.push((None, *value));
                    current = parent;
                }
            }
        }
        if !current.is_anon() {
            self.preview = true;
            self.text.write_str("<name-prefix>.")?;
        }
        if parts.is_empty() {
            self.text.write_str("<anonymous>")?;
        }
        for (i, (part, number)) in parts.iter().rev().enumerate() {
            if i != 0 {
                self.text.write_char('.')?;
            }
            match part {
                Some(s) => self.text_preview(s)?,
                None => write!(self.text, "{number}")?,
            }
        }
        Ok(())
    }
    fn error(&mut self, error: &'a TypeError) -> fmt::Result {
        use TypeError::*;
        match error {
            TypeMismatch {
                expected, inferred, ..
            } => {
                self.text.write_str("TypeMismatch { expected: ")?;
                self.expr(expected, 0)?;
                self.text.write_str(", inferred: ")?;
                self.expr(inferred, 0)?;
                self.text.write_str(" }")?;
            }
            NotAFunction { ty, .. } | ExpectedSort { ty, .. } => {
                self.text
                    .write_str(if matches!(error, NotAFunction { .. }) {
                        "NotAFunction { type: "
                    } else {
                        "ExpectedSort { type: "
                    })?;
                self.expr(ty, 0)?;
                self.text.write_str(" }")?;
            }
            InvalidProjNotStruct(ty) => {
                self.text.write_str("InvalidProjNotStruct { type: ")?;
                self.expr(ty, 0)?;
                self.text.write_str(" }")?;
            }
            UnboundVariable(i) => write!(self.text, "UnboundVariable({i})")?,
            UnknownFVar(i) => write!(self.text, "UnknownFVar({})", i.as_u64())?,
            UnknownConst(name) | InvalidProjNotUniqueConstructor(name) | UnknownInductive(name) => {
                self.text.write_str(match error {
                    UnknownConst(_) => "UnknownConst(",
                    InvalidProjNotUniqueConstructor(_) => "InvalidProjNotUniqueConstructor(",
                    _ => "UnknownInductive(",
                })?;
                self.name(name)?;
                self.text.write_char(')')?;
            }
            SortDepthExceeded { depth } => {
                write!(self.text, "SortDepthExceeded {{ depth: {depth} }}")?
            }
            InvalidProjIndexOutOfBounds(i, n) => {
                write!(self.text, "InvalidProjIndexOutOfBounds({i}, {n})")?
            }
            InvalidProjWrongArgCount {
                got,
                expected,
                num_params,
                num_indices,
            } => write!(
                self.text,
                "InvalidProjWrongArgCount {{ got: {got}, expected: {expected}, num_params: {num_params}, num_indices: {num_indices} }}"
            )?,
            InvalidProjFromProp { field_idx } => write!(
                self.text,
                "InvalidProjFromProp {{ field_idx: {field_idx} }}"
            )?,
            ModeRequired { feature, mode } => {
                self.text.write_str("ModeRequired { feature: ")?;
                self.text_preview(feature)?;
                self.text.write_str(", mode: ")?;
                self.text_preview(mode)?;
                self.text.write_str(" }")?;
            }
            LevelCountMismatch {
                name,
                expected,
                got,
            } => {
                self.text.write_str("LevelCountMismatch { name: ")?;
                self.name(name)?;
                write!(self.text, ", expected: {expected}, got: {got} }}")?;
            }
            HeartbeatExceeded { limit, profile } => {
                self.preview |= profile.is_some();
                write!(
                    self.text,
                    "HeartbeatExceeded {{ limit: {limit}, profile_present: {} }}",
                    profile.is_some()
                )?;
            }
            DeclarationBudgetExhausted { limit } => write!(
                self.text,
                "DeclarationBudgetExhausted {{ limit: {limit} }}; no verdict"
            )?,
            ExcessiveMemory => self.text.write_str("ExcessiveMemory")?,
            DeepRecursion => self.text.write_str("DeepRecursion")?,
            Interrupted => self.text.write_str("Interrupted")?,
            UndefinedLevelParam { param } => {
                self.text.write_str("UndefinedLevelParam(")?;
                self.name(param)?;
                self.text.write_char(')')?;
            }
            UnsafeDeclaration { name }
            | PartialDeclaration { name }
            | LevelSharingDependent { name } => {
                self.text.write_str(match error {
                    UnsafeDeclaration { .. } => "UnsafeDeclaration(",
                    PartialDeclaration { .. } => "PartialDeclaration(",
                    _ => "LevelSharingDependent(",
                })?;
                self.name(name)?;
                self.text.write_char(')')?;
            }
        }
        if let Some(location) = error.location() {
            self.text.write_str("; location { declaration: ")?;
            if let Some(name) = &location.decl_name {
                self.name(name)?;
            } else {
                self.text.write_str("none")?;
            }
            write!(self.text, ", steps: {}, preview: [", location.steps.len())?;
            for step in location.steps.iter().take(LIST_PREVIEW_ITEMS) {
                write!(self.text, "{step:?},")?;
            }
            if location.steps.len() > LIST_PREVIEW_ITEMS {
                self.preview = true;
                self.text.write_str("<more>")?;
            }
            self.text.write_str("] }")?;
        }
        Ok(())
    }
    fn expression(&mut self, expr: &'a Expr, depth: usize) -> fmt::Result {
        use ExprKind::*;
        match expr.kind() {
            BVar(i) => write!(self.text, "BVar({i})"),
            FVar(i) => write!(self.text, "FVar({})", i.as_u64()),
            Sort(level) => {
                self.text.write_str("Sort(")?;
                self.reference(Node::Level(level), depth + 1)?;
                self.text.write_char(')')
            }
            Const(name, levels) => {
                self.text.write_str("Const(")?;
                self.name(name)?;
                self.text.write_str(", levels=[")?;
                for level in levels.iter().take(LIST_PREVIEW_ITEMS) {
                    self.reference(Node::Level(level), depth + 1)?;
                    self.text.write_char(',')?;
                }
                if levels.len() > LIST_PREVIEW_ITEMS {
                    self.preview = true;
                    write!(self.text, "<{} more>", levels.len() - LIST_PREVIEW_ITEMS)?;
                }
                self.text.write_str("])")
            }
            App(f, a) => {
                self.text.write_str("App(")?;
                self.expr(f, depth + 1)?;
                self.text.write_str(", ")?;
                self.expr(a, depth + 1)?;
                self.text.write_char(')')
            }
            Lam(b, t, e) | Pi(b, t, e) => {
                write!(
                    self.text,
                    "{}({:?}, ",
                    if matches!(expr.kind(), Lam(..)) {
                        "Lam"
                    } else {
                        "Pi"
                    },
                    b
                )?;
                self.expr(t, depth + 1)?;
                self.text.write_str(", ")?;
                self.expr(e, depth + 1)?;
                self.text.write_char(')')
            }
            Let(name, t, v, e, nondep) => {
                self.text.write_str("Let(")?;
                self.name(name)?;
                self.text.write_str(", ")?;
                self.expr(t, depth + 1)?;
                self.text.write_str(", ")?;
                self.expr(v, depth + 1)?;
                self.text.write_str(", ")?;
                self.expr(e, depth + 1)?;
                write!(self.text, ", nondep={nondep})")
            }
            Lit(Literal::Nat(BigNat::Small(n))) => write!(self.text, "Nat({n})"),
            Lit(Literal::Nat(BigNat::Big(limbs))) => {
                self.preview = true;
                write!(self.text, "Nat(<limbs={}, low=[", limbs.len())?;
                for n in limbs.iter().take(2) {
                    write!(self.text, "{n:x},")?;
                }
                self.text.write_str("]; preview>)")
            }
            Lit(Literal::String(s)) => {
                self.text.write_str("String(")?;
                self.text_preview(s)?;
                self.text.write_char(')')
            }
            Proj(name, i, e) => {
                self.text.write_str("Proj(")?;
                self.name(name)?;
                write!(self.text, ", {i}, ")?;
                self.expr(e, depth + 1)?;
                self.text.write_char(')')
            }
            MData(data, e) => {
                self.preview |= !data.is_empty();
                write!(
                    self.text,
                    "MData(<{} metadata entries omitted>, ",
                    data.len()
                )?;
                self.expr(e, depth + 1)?;
                self.text.write_char(')')
            }
            SProp => self.text.write_str("SProp"),
            Squash(e) | CubicalPathLam { body: e } => {
                self.text.write_str(if matches!(expr.kind(), Squash(_)) {
                    "Squash("
                } else {
                    "CubicalPathLam("
                })?;
                self.expr(e, depth + 1)?;
                self.text.write_char(')')
            }
            CubicalInterval => self.text.write_str("CubicalInterval"),
            CubicalI0 => self.text.write_str("CubicalI0"),
            CubicalI1 => self.text.write_str("CubicalI1"),
            CubicalPath { ty, left, right } => {
                self.children("CubicalPath", &[ty, left, right], depth)
            }
            CubicalPathApp { path, arg } => self.children("CubicalPathApp", &[path, arg], depth),
            CubicalHComp { ty, phi, u, base } => {
                self.children("CubicalHComp", &[ty, phi, u, base], depth)
            }
            CubicalTransp { ty, phi, base } => {
                self.children("CubicalTransp", &[ty, phi, base], depth)
            }
            CubicalCoe { ty, r, s, base } => self.children("CubicalCoe", &[ty, r, s, base], depth),
            ZFCMem { element, set } => self.children("ZFCMem", &[element, set], depth),
            ZFCComprehension { domain, pred } => {
                self.children("ZFCComprehension", &[domain, pred], depth)
            }
            ZFCSet(set) => match set {
                ZFCSetExpr::Empty => self.text.write_str("ZFCSet::Empty"),
                ZFCSetExpr::Infinity => self.text.write_str("ZFCSet::Infinity"),
                ZFCSetExpr::Singleton(e) => self.children("ZFCSet::Singleton", &[e], depth),
                ZFCSetExpr::Pair(a, b) => self.children("ZFCSet::Pair", &[a, b], depth),
                ZFCSetExpr::Union(e) => self.children("ZFCSet::Union", &[e], depth),
                ZFCSetExpr::PowerSet(e) => self.children("ZFCSet::PowerSet", &[e], depth),
                ZFCSetExpr::Separation { set, pred } => {
                    self.children("ZFCSet::Separation", &[set, pred], depth)
                }
                ZFCSetExpr::Replacement { set, func } => {
                    self.children("ZFCSet::Replacement", &[set, func], depth)
                }
                ZFCSetExpr::Choice(e) => self.children("ZFCSet::Choice", &[e], depth),
            },
        }
    }
    fn children(
        &mut self,
        label: &str,
        children: &[&'a std::sync::Arc<Expr>],
        depth: usize,
    ) -> fmt::Result {
        write!(self.text, "{label}(")?;
        for (i, child) in children.iter().enumerate() {
            if i != 0 {
                self.text.write_str(", ")?;
            }
            self.expr(child, depth + 1)?;
        }
        self.text.write_char(')')
    }
    fn level(&mut self, level: &'a Level, depth: usize) -> fmt::Result {
        match level {
            Level::Zero => self.text.write_str("Level::Zero"),
            Level::Param(name) => {
                self.text.write_str("Level::Param(")?;
                self.name(name)?;
                self.text.write_char(')')
            }
            Level::Succ(child) => {
                self.text.write_str("Level::Succ(")?;
                self.reference(Node::Level(child), depth + 1)?;
                self.text.write_char(')')
            }
            Level::Max(a, b) | Level::IMax(a, b) => {
                self.text.write_str(if matches!(level, Level::Max(..)) {
                    "Level::Max("
                } else {
                    "Level::IMax("
                })?;
                self.reference(Node::Level(a), depth + 1)?;
                self.text.write_str(", ")?;
                self.reference(Node::Level(b), depth + 1)?;
                self.text.write_char(')')
            }
        }
    }
    fn finish(mut self) -> String {
        let mut index = 0;
        while index < self.nodes.len() && !self.text.full {
            let (node, depth) = self.nodes[index];
            if write!(self.text, "\n#{index} = ").is_err() {
                break;
            }
            let result = match node {
                Node::Expr(e) => self.expression(e, depth),
                Node::Level(l) => self.level(l, depth),
            };
            if result.is_err() {
                break;
            }
            index += 1;
        }
        if self.text.full || self.node_limit || self.depth_limit || self.preview {
            // The body reserved enough space for this fixed-size footer.
            let footer = format!(
                "\n[diagnostic elided: bytes={}, nodes={}, depth={}, previews={}]",
                self.text.full, self.node_limit, self.depth_limit, self.preview
            );
            self.text.value.push_str(&footer);
        }
        self.text.value
    }
}

fn render(root: &Root<'_>) -> String {
    let mut renderer = Renderer::new();
    let _ = match root {
        Root::Expr(e) => renderer.expr(e, 0),
        Root::Error(e) => renderer.error(e),
    };
    renderer.finish()
}
