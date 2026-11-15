// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Persistent labelled syntax. Labels are never stored in a node-identity table.
use crate::expr::{stack_safe, BinderData, Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// A domain actually checked, or an explicitly named construction hole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Label {
    /// The application's argument was checked against this domain.
    Checked(Term),
    /// The producer has no annotation for this construction.
    Missing(String),
}

/// C4's untrusted syntax, with a cached canonical erasure and diagnostic syntax
/// before universe instantiation. The latter is transformed by term substitution
/// too, but deliberately not by universe substitution. It has no proof meaning.
#[derive(Clone, Debug)]
pub struct Term(pub Arc<Node>, Expr, Option<Arc<Expr>>, Metadata);
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Head {
    Constant(Name),
    Local(u32),
    Variable,
    Other,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Metadata {
    head: Head,
    built_head: Head,
    minor: Option<Name>,
    height: u32,
    // Maximum free bound-variable index plus one, including application labels.
    loose_bvar_range: u64,
}
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        stack_safe(|| self.labelled_eq(other))
    }
}
impl Eq for Term {}
// Hash by cached erasure, then resolve collisions with full labelled equality.
// Different annotations therefore NEVER become the same active search pair.
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.1.hash(state);
    }
}

/// The design's core plus literal/projection extensions used to survey Init.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    /// Bound variable, indexed from the innermost binder.
    BVar(u32),
    /// Context variable, a level counted from the oldest entry.
    Local(u32),
    /// Universe sort.
    Sort(Level),
    /// Constant and its universe arguments.
    Const(Name, Vec<Level>),
    /// Literal extension (design S6).
    Lit(Literal),
    /// Projection extension (design S4).
    Proj(Name, u32, Term),
    /// Application carrying its domain.
    App(Term, Term, Label),
    /// Lambda binder.
    Lam(BinderData, Term, Term),
    /// Pi binder.
    Pi(BinderData, Term, Term),
    /// Let binder.
    Let(Name, Term, Term, Term),
}

// A per-transform work table, not a store of application annotations. Include
// provenance and context depth: the same Node can carry different diagnostics.
#[derive(PartialEq, Eq, Hash)]
struct TransformKey {
    node: *const Node,
    under: u32,
    before_levels: Option<Arc<Expr>>,
    metadata: Metadata,
}

enum Transform<'a> {
    Substitute(&'a Term),
    Lift(u32),
    Abstract(u32),
    Levels(&'a [Name], &'a [Level]),
    Minor(&'a Name, u32, u32),
}

impl Term {
    // A labelled term is a DAG. Derived recursive equality unfolds shared
    // children repeatedly: App(t,t,Checked(t)) costs three comparisons of t.
    // Compare each node pair once while retaining full annotation equality.
    fn labelled_eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        let mut pending = vec![(self, other)];
        let mut seen = HashSet::new();
        while let Some((left, right)) = pending.pop() {
            if Arc::ptr_eq(&left.0, &right.0) {
                continue;
            }
            let pair = (Arc::as_ptr(&left.0), Arc::as_ptr(&right.0));
            if !seen.insert(pair) {
                continue;
            }
            match (left.0.as_ref(), right.0.as_ref()) {
                (Node::BVar(a), Node::BVar(b)) | (Node::Local(a), Node::Local(b)) => {
                    if a != b {
                        return false;
                    }
                }
                (Node::Sort(a), Node::Sort(b)) => {
                    if a != b {
                        return false;
                    }
                }
                (Node::Const(a, ls), Node::Const(b, rs)) => {
                    if a != b || ls != rs {
                        return false;
                    }
                }
                (Node::Lit(a), Node::Lit(b)) => {
                    if a != b {
                        return false;
                    }
                }
                (Node::Proj(a, i, x), Node::Proj(b, j, y)) => {
                    if a != b || i != j {
                        return false;
                    }
                    pending.push((x, y));
                }
                (Node::App(f, a, d), Node::App(g, b, e)) => {
                    match (d, e) {
                        (Label::Checked(d), Label::Checked(e)) => pending.push((d, e)),
                        (Label::Missing(a), Label::Missing(b)) if a == b => {}
                        _ => return false,
                    }
                    pending.push((a, b));
                    pending.push((f, g));
                }
                (Node::Lam(a, d, b), Node::Lam(c, e, f))
                | (Node::Pi(a, d, b), Node::Pi(c, e, f)) => {
                    if a != c {
                        return false;
                    }
                    pending.push((b, f));
                    pending.push((d, e));
                }
                (Node::Let(a, d, v, b), Node::Let(c, e, w, f)) => {
                    if a != c {
                        return false;
                    }
                    pending.push((b, f));
                    pending.push((v, w));
                    pending.push((d, e));
                }
                _ => return false,
            }
        }
        true
    }

    /// Allocate a node and cache its erasure. Binder annotations and let names
    /// are erased as in the design; the Rust node keeps them for diagnostics.
    pub fn new(node: Node) -> Self {
        let erased = match &node {
            Node::BVar(i) => Expr::bvar(*i),
            Node::Local(i) => Expr::fvar(crate::expr::FVarId(u64::from(*i))),
            Node::Sort(l) => Expr::sort(l.clone()),
            Node::Const(n, ls) => Expr::const_(n.clone(), ls.clone()),
            Node::Lit(l) => Expr::from_kind(ExprKind::Lit(l.clone())),
            Node::Proj(n, i, e) => Expr::proj(n.clone(), *i, e.erase()),
            Node::App(f, a, _) => Expr::app(f.erase(), a.erase()),
            Node::Lam(_, d, b) => Expr::lam(BinderData::default(), d.erase(), b.erase()),
            Node::Pi(_, d, b) => Expr::pi(BinderData::default(), d.erase(), b.erase()),
            Node::Let(_, t, v, b) => Expr::let_named(
                Name::from_string("_trace"),
                t.erase(),
                v.erase(),
                b.erase(),
                false,
            ),
        };
        let head = match &node {
            Node::Const(n, _) => Head::Constant(n.clone()),
            Node::Local(i) => Head::Local(*i),
            Node::BVar(_) => Head::Variable,
            Node::App(f, _, _) => f.3.head.clone(),
            _ => Head::Other,
        };
        let child_height = match &node {
            Node::App(f, a, label) => f.height().max(a.height()).max(match label {
                Label::Checked(d) => d.height(),
                Label::Missing(_) => 0,
            }),
            Node::Lam(_, d, b) | Node::Pi(_, d, b) => d.height().max(b.height()),
            Node::Let(_, t, v, b) => t.height().max(v.height()).max(b.height()),
            Node::Proj(_, _, e) => e.height(),
            _ => 0,
        };
        let loose_bvar_range = match &node {
            Node::BVar(i) => u64::from(*i) + 1,
            Node::App(f, a, label) => {
                f.3.loose_bvar_range
                    .max(a.3.loose_bvar_range)
                    .max(match label {
                        Label::Checked(d) => d.3.loose_bvar_range,
                        Label::Missing(_) => 0,
                    })
            }
            Node::Lam(_, d, b) | Node::Pi(_, d, b) => {
                d.3.loose_bvar_range
                    .max(b.3.loose_bvar_range.saturating_sub(1))
            }
            Node::Let(_, t, v, b) => {
                t.3.loose_bvar_range
                    .max(v.3.loose_bvar_range)
                    .max(b.3.loose_bvar_range.saturating_sub(1))
            }
            Node::Proj(_, _, e) => e.3.loose_bvar_range,
            _ => 0,
        };
        Self(
            Arc::new(node),
            erased,
            None,
            Metadata {
                head: head.clone(),
                built_head: head,
                minor: None,
                height: child_height.saturating_add(1),
                loose_bvar_range,
            },
        )
    }
    /// Height of the actual labelled syntax, excluding diagnostic provenance.
    pub fn height(&self) -> u32 {
        self.3.height
    }
    /// Preserve an existing application's construction identity when rebuilding
    /// its reduced head. This is diagnostic metadata, not a label side table.
    pub fn with_origin_of(mut self, old: &Self) -> Self {
        self.3.built_head = old.3.built_head.clone();
        self.3.minor = old.3.minor.clone();
        self
    }
    /// Whether this application was built with a different head before reduction.
    pub fn had_other_head(&self, current: &Name) -> bool {
        let mut node = self;
        while let Node::App(function, _, _) = node.0.as_ref() {
            if !matches!(&node.3.built_head,Head::Constant(n) if n==current) {
                return true;
            }
            node = function;
        }
        false
    }
    /// Recursor whose generic RHS built this minor-premise application.
    pub fn minor_origin(&self) -> Option<&Name> {
        self.3.minor.as_ref()
    }
    /// Mark the minor-premise applications in a generic rule before its binders
    /// are instantiated. Their original local levels survive abstraction.
    pub fn mark_minor_heads(&self, recursor: &Name, start: u32, count: u32) -> Self {
        self.map(
            0,
            &Transform::Minor(recursor, start, start.saturating_add(count)),
        )
    }
    /// Canonical, diagnostic locally nameless erasure (locals become FVars).
    /// This is not the byte interface to the proved checker.
    pub fn erase(&self) -> Expr {
        self.1.clone()
    }
    /// Equality after dropping labels, binder flags and names.
    pub fn erased_eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
    /// Syntax before the recorded universe substitutions, after the SAME term
    /// substitutions/weakening/abstraction as the actual term.
    pub fn before_levels(&self) -> &Expr {
        self.2.as_deref().unwrap_or(&self.1)
    }
    /// Capture-avoiding substitution, including every label and its provenance.
    pub fn instantiate(&self, value: &Self) -> Self {
        self.map(0, &Transform::Substitute(value))
    }
    /// Open a binder with a stable context level.
    pub fn open(&self, level: u32) -> Self {
        self.instantiate(&Self::new(Node::Local(level)))
    }
    /// Lift bound variables; context levels stay unchanged.
    pub fn lift(&self, amount: u32, from: u32) -> Self {
        if amount == 0 {
            return self.clone();
        }
        self.map(from, &Transform::Lift(amount))
    }
    /// Abstract a context level in terms, labels and provenance.
    pub fn abstract_local(&self, level: u32) -> Self {
        self.map(0, &Transform::Abstract(level))
    }
    /// Instantiate universes in the actual syntax and labels, retaining the
    /// pre-instantiation syntax separately for the R2 classifier.
    pub fn instantiate_levels(&self, params: &[Name], levels: &[Level]) -> Self {
        if params.is_empty() {
            return self.clone();
        }
        self.map(0, &Transform::Levels(params, levels))
    }
    fn map(&self, under: u32, operation: &Transform<'_>) -> Self {
        self.map_cached(under, operation, &mut HashMap::new())
    }
    fn map_cached(
        &self,
        under: u32,
        operation: &Transform<'_>,
        work: &mut HashMap<TransformKey, Self>,
    ) -> Self {
        // Reuse unchanged labelled syntax. Erasure alone is insufficient: a
        // free variable can occur only in an application's stored domain.
        if matches!(operation, Transform::Substitute(_) | Transform::Lift(_))
            && self.3.loose_bvar_range <= u64::from(under)
        {
            return self.clone();
        }
        let key = TransformKey {
            node: Arc::as_ptr(&self.0),
            under,
            before_levels: self.2.clone(),
            metadata: self.3.clone(),
        };
        if let Some(mapped) = work.get(&key) {
            return mapped.clone();
        }
        let mapped = stack_safe(|| self.map_inner(under, operation, work));
        work.insert(key, mapped.clone());
        mapped
    }
    fn map_inner(
        &self,
        under: u32,
        operation: &Transform<'_>,
        work: &mut HashMap<TransformKey, Self>,
    ) -> Self {
        match (self.0.as_ref(), operation) {
            (Node::BVar(i), Transform::Substitute(value)) if *i == under => {
                return value.lift(under, 0)
            }
            _ => {}
        }
        let mut map = |t: &Term, depth| t.map_cached(depth, operation, work);
        let node = match self.0.as_ref() {
            Node::BVar(i) => Node::BVar(match operation {
                Transform::Substitute(_) if *i > under => i - 1,
                Transform::Lift(amount) if *i >= under => i.saturating_add(*amount),
                _ => *i,
            }),
            Node::Local(i) => match operation {
                Transform::Abstract(level) if i == level => Node::BVar(under),
                _ => Node::Local(*i),
            },
            Node::Sort(l) => {
                if let Transform::Levels(params, levels) = operation {
                    let e = self.1.instantiate_level_params_direct(params, levels);
                    if let ExprKind::Sort(mapped) = e.kind() {
                        Node::Sort(mapped.clone())
                    } else {
                        Node::Sort(l.clone())
                    }
                } else {
                    Node::Sort(l.clone())
                }
            }
            Node::Const(n, ls) => {
                if let Transform::Levels(params, levels) = operation {
                    let e = self.1.instantiate_level_params_direct(params, levels);
                    if let ExprKind::Const(mapped, ls) = e.kind() {
                        Node::Const(mapped.clone(), ls.to_vec())
                    } else {
                        Node::Const(n.clone(), ls.clone())
                    }
                } else {
                    Node::Const(n.clone(), ls.clone())
                }
            }
            Node::Lit(l) => Node::Lit(l.clone()),
            Node::Proj(n, i, e) => Node::Proj(n.clone(), *i, map(e, under)),
            Node::App(f, a, label) => Node::App(
                map(f, under),
                map(a, under),
                match label {
                    Label::Checked(d) => Label::Checked(map(d, under)),
                    Label::Missing(source) => Label::Missing(source.clone()),
                },
            ),
            Node::Lam(b, d, t) => Node::Lam(*b, map(d, under), map(t, under.saturating_add(1))),
            Node::Pi(b, d, t) => Node::Pi(*b, map(d, under), map(t, under.saturating_add(1))),
            Node::Let(n, t, v, b) => Node::Let(
                n.clone(),
                map(t, under),
                map(v, under),
                map(b, under.saturating_add(1)),
            ),
        };
        let mut result = Self::new(node).with_origin_of(self);
        if let Transform::Minor(recursor, start, end) = operation {
            if matches!(self.0.as_ref(), Node::App(..))
                && matches!(&self.3.built_head,Head::Local(i) if *i>=*start && *i<*end)
            {
                result.3.minor = Some((*recursor).clone());
            }
        }
        result.2 = match operation {
            Transform::Levels(..) => {
                Some(self.2.clone().unwrap_or_else(|| Arc::new(self.1.clone())))
            }
            _ => self.2.as_ref().map(|old| {
                Arc::new(match operation {
                    Transform::Substitute(value) => {
                        old.instantiate_at(value.before_levels(), under)
                    }
                    Transform::Lift(amount) => old.lift_from(under, *amount),
                    Transform::Abstract(level) => {
                        // Wrapping makes the kernel's pure abstraction start at
                        // this node's binder depth, preserving existing indices.
                        let mut wrapped = old.as_ref().clone();
                        for _ in 0..under {
                            wrapped = Expr::lam(
                                BinderData::default(),
                                Expr::sort(Level::zero()),
                                wrapped,
                            );
                        }
                        let mut abstracted =
                            wrapped.abstract_fvar(crate::expr::FVarId(u64::from(*level)));
                        for _ in 0..under {
                            if let ExprKind::Lam(_, _, body) = abstracted.kind() {
                                abstracted = body.as_ref().clone();
                            }
                        }
                        abstracted
                    }
                    Transform::Levels(..) | Transform::Minor(..) => old.as_ref().clone(),
                })
            }),
        };
        result
    }
}

// Drain uniquely owned nodes iteratively. Cached erasures and provenance use
// Expr's existing stack-safe teardown; no unsafe code or node-identity labels.
impl Drop for Node {
    fn drop(&mut self) {
        static LEAF: std::sync::LazyLock<Arc<Node>> =
            std::sync::LazyLock::new(|| Arc::new(Node::BVar(0)));
        fn children(node: &mut Node, work: &mut Vec<Arc<Node>>) {
            let mut take =
                |term: &mut Term| work.push(std::mem::replace(&mut term.0, LEAF.clone()));
            match node {
                Node::App(f, a, label) => {
                    take(f);
                    take(a);
                    if let Label::Checked(d) = label {
                        take(d);
                    }
                }
                Node::Lam(_, d, b) | Node::Pi(_, d, b) => {
                    take(d);
                    take(b);
                }
                Node::Let(_, t, v, b) => {
                    take(t);
                    take(v);
                    take(b);
                }
                Node::Proj(_, _, e) => take(e),
                _ => {}
            }
        }
        let mut work = Vec::new();
        children(self, &mut work);
        while let Some(arc) = work.pop() {
            if let Ok(mut node) = Arc::try_unwrap(arc) {
                children(&mut node, &mut work);
            }
        }
    }
}
