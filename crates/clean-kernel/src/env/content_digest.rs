// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A stable, order-independent CONTENT digest of an [`Environment`].
//!
//! Diagnostic only — nothing in checking reads it. It exists to PROVE that a
//! change to how the environment is BUILT (the `.olean` import passes) left
//! what was built unchanged: take the digest before and after on the same
//! input and compare the bytes. `clean check` writes it when
//! `CLEAN_CHECK_ENV_DIGEST_OUT` names a file.
//!
//! Every table is digested per ENTRY (key → 128-bit digest of its content)
//! and the entry lines are sorted before a table is hashed, so hash-map
//! iteration order never reaches the result. Expressions are hashed
//! STRUCTURALLY and bottom-up; a subterm reached through a shared `Arc` is
//! memoised by address, so an imported proof DAG costs its node count, never
//! the size of the tree it unfolds to.
//!
//! Deliberately NOT digested: the mutation counters (`generation`,
//! `simp_registry_revision`), the lazy constant source, native reducer
//! FUNCTIONS (their names are), the per-feature `*_init` prelude flags, the
//! aesop rule sets (only their sizes), and typed extension states that export
//! nothing, except the value binder name table, which the import passes write
//! and which is digested as its own section. Each of the others is either a
//! counter, code, or state the import passes never write.

use super::Environment;
use crate::expr::{Expr, ExprKind, Literal, MDataValue, ZFCSetExpr};
use crate::level::Level;
use crate::name::{Name, NameInner};
use hashbrown::HashMap;
use sha2::{Digest, Sha256};
use std::fmt::Write as _;
use std::sync::Arc;

/// Digest of one environment table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvDigestSection {
    /// Table name (stable, used as the report key).
    pub name: &'static str,
    /// Sorted `(entry key, entry digest hex)` lines.
    pub entries: Vec<(String, String)>,
    /// SHA-256 over the sorted entry lines, hex.
    pub sha256: String,
}

/// The full content digest: one section per table plus a total.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvContentDigest {
    /// Per-table digests in a fixed order.
    pub sections: Vec<EnvDigestSection>,
    /// SHA-256 over every section's `(name, count, sha256)` line, hex.
    pub total: String,
}

impl EnvContentDigest {
    /// One line per section plus the total — the form to compare.
    #[must_use]
    pub fn render_summary(&self) -> String {
        let mut out = String::from("clean-env-content-digest v1\n");
        for s in &self.sections {
            let _ = writeln!(
                out,
                "{} count={} sha256={}",
                s.name,
                s.entries.len(),
                s.sha256
            );
        }
        let _ = writeln!(out, "total sha256={}", self.total);
        out
    }

    /// Every entry line, `section<TAB>key<TAB>digest` — the form to DIFF when
    /// two summaries disagree.
    #[must_use]
    pub fn render_entries(&self) -> String {
        let mut out = String::new();
        for s in &self.sections {
            for (key, digest) in &s.entries {
                let _ = writeln!(out, "{}\t{key}\t{digest}", s.name);
            }
        }
        out
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes
        .iter()
        .fold(String::with_capacity(bytes.len() * 2), |mut s, b| {
            let _ = write!(s, "{b:02x}");
            s
        })
}

/// Length-prefixed field writer over SHA-256, so adjacent fields can never
/// run together (`"ab" + "c"` and `"a" + "bc"` hash differently).
struct Fields(Sha256);

impl Fields {
    fn new(tag: &str) -> Self {
        let mut f = Fields(Sha256::new());
        f.bytes(tag.as_bytes());
        f
    }
    fn bytes(&mut self, b: &[u8]) {
        self.0.update((b.len() as u64).to_le_bytes());
        self.0.update(b);
    }
    fn u64(&mut self, v: u64) {
        self.0.update(v.to_le_bytes());
    }
    fn name(&mut self, n: &Name) {
        self.bytes(&name_bytes(n));
    }
    fn names(&mut self, ns: &[Name]) {
        self.u64(ns.len() as u64);
        for n in ns {
            self.name(n);
        }
    }
    fn level(&mut self, l: &Level) {
        self.bytes(&level_bytes(l));
    }
    fn debug(&mut self, v: &impl std::fmt::Debug) {
        self.bytes(format!("{v:?}").as_bytes());
    }
    fn finish16(self) -> [u8; 16] {
        let full = self.0.finalize();
        let mut out = [0u8; 16];
        out.copy_from_slice(&full[..16]);
        out
    }
    fn finish_hex(self) -> String {
        hex(&self.0.finalize())
    }
    fn finish32(self) -> [u8; 32] {
        self.0.finalize().into()
    }
}

/// SHA-256 content digest of one [`super::Declaration`], with the same
/// structural expression encoding as [`Environment::content_digest`] (bottom-up,
/// shared subterms memoised by address). Used by the reference entry
/// (`crate::reference`) as the `decl_digest` of the token it issues.
pub(crate) fn declaration_content_digest(decl: &super::Declaration) -> [u8; 32] {
    use super::Declaration;
    let mut ed = ExprDigester::default();
    let (tag, name, level_params, type_, value, reducible) = match decl {
        Declaration::Definition {
            name,
            level_params,
            type_,
            value,
            is_reducible,
        } => ("def", name, level_params, type_, Some(value), *is_reducible),
        Declaration::Axiom {
            name,
            level_params,
            type_,
        } => ("axiom", name, level_params, type_, None, false),
        Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
        } => ("theorem", name, level_params, type_, Some(value), false),
        Declaration::Opaque {
            name,
            level_params,
            type_,
            value,
        } => ("opaque", name, level_params, type_, Some(value), false),
    };
    let mut f = Fields::new("clean.reference.decl.v1");
    f.bytes(tag.as_bytes());
    f.name(name);
    f.names(level_params);
    ed.opt(&mut f, Some(type_));
    ed.opt(&mut f, value);
    f.u64(u64::from(reducible));
    f.finish32()
}

/// SHA-256 content digest of an inductive family block (the reference
/// entry's `add_inductive_checked`), encoded as [`declaration_content_digest`]:
/// level parameters, parameter count, then each type's name and type and each
/// of its constructors' names and types, in declaration order.
pub(crate) fn inductive_content_digest(decl: &crate::inductive::InductiveDecl) -> [u8; 32] {
    let mut ed = ExprDigester::default();
    let mut f = Fields::new("clean.reference.inductive.v1");
    f.names(&decl.level_params);
    f.u64(u64::from(decl.num_params));
    f.u64(decl.types.len() as u64);
    for ty in &decl.types {
        f.name(&ty.name);
        ed.opt(&mut f, Some(&ty.type_));
        f.u64(ty.constructors.len() as u64);
        for ctor in &ty.constructors {
            f.name(&ctor.name);
            ed.opt(&mut f, Some(&ctor.type_));
        }
    }
    f.finish32()
}

/// SHA-256 content digest of the kernel's quotient primitives as installed
/// (the reference entry's `add_quot_checked`): each primitive's name, level
/// parameters and type, in the order given.
pub(crate) fn quotient_content_digest(prims: &[(&Name, &[Name], &Expr)]) -> [u8; 32] {
    let mut ed = ExprDigester::default();
    let mut f = Fields::new("clean.reference.quot.v1");
    f.u64(prims.len() as u64);
    for (name, levels, ty) in prims {
        f.name(name);
        f.names(levels);
        ed.opt(&mut f, Some(ty));
    }
    f.finish32()
}

/// SHA-256 content digest of a closed `(type, value)` pair (the reference
/// entry's `check_closed_term`), encoded as [`declaration_content_digest`].
pub(crate) fn closed_term_content_digest(ty: &Expr, val: &Expr) -> [u8; 32] {
    let mut ed = ExprDigester::default();
    let mut f = Fields::new("clean.reference.closed-term.v1");
    ed.opt(&mut f, Some(ty));
    ed.opt(&mut f, Some(val));
    f.finish32()
}

/// Structural, unambiguous encoding of a name (quoted and numeric components
/// never collide with a dotted display string).
fn name_bytes(n: &Name) -> Vec<u8> {
    let mut parts: Vec<Vec<u8>> = Vec::new();
    let mut cur = n;
    loop {
        match cur.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, s) => {
                let mut p = vec![b's'];
                p.extend_from_slice(&(s.len() as u64).to_le_bytes());
                p.extend_from_slice(s.as_bytes());
                parts.push(p);
                cur = parent;
            }
            NameInner::Num(parent, k) => {
                let mut p = vec![b'n'];
                p.extend_from_slice(&k.to_le_bytes());
                parts.push(p);
                cur = parent;
            }
        }
    }
    parts.into_iter().rev().flatten().collect()
}

fn level_bytes(l: &Level) -> Vec<u8> {
    let mut out = Vec::new();
    let mut stack = vec![l];
    while let Some(cur) = stack.pop() {
        match cur {
            Level::Zero => out.push(b'z'),
            Level::Succ(a) => {
                out.push(b'S');
                stack.push(&**a);
            }
            Level::Max(a, b) | Level::IMax(a, b) => {
                out.push(if matches!(cur, Level::Max(..)) {
                    b'M'
                } else {
                    b'I'
                });
                stack.push(&**b);
                stack.push(&**a);
            }
            Level::Param(n) => {
                out.push(b'p');
                let nb = name_bytes(n);
                out.extend_from_slice(&(nb.len() as u64).to_le_bytes());
                out.extend_from_slice(&nb);
            }
        }
    }
    out
}

/// Direct `Arc` children of a node, in a fixed order.
fn children(e: &Expr) -> Vec<&Arc<Expr>> {
    match e.kind() {
        ExprKind::App(f, a) => vec![f, a],
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => vec![t, b],
        ExprKind::Let(_, t, v, b, _) => vec![t, v, b],
        ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) | ExprKind::Squash(x) => vec![x],
        ExprKind::CubicalPath { ty, left, right } => vec![ty, left, right],
        ExprKind::CubicalPathLam { body } => vec![body],
        ExprKind::CubicalPathApp { path, arg } => vec![path, arg],
        ExprKind::CubicalHComp { ty, phi, u, base } => vec![ty, phi, u, base],
        ExprKind::CubicalTransp { ty, phi, base } => vec![ty, phi, base],
        ExprKind::CubicalCoe { ty, r, s, base } => vec![ty, r, s, base],
        ExprKind::ZFCSet(set) => match set {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => vec![],
            ZFCSetExpr::Singleton(a)
            | ZFCSetExpr::Union(a)
            | ZFCSetExpr::PowerSet(a)
            | ZFCSetExpr::Choice(a) => vec![a],
            ZFCSetExpr::Pair(a, b)
            | ZFCSetExpr::Separation { set: a, pred: b }
            | ZFCSetExpr::Replacement { set: a, func: b } => vec![a, b],
        },
        ExprKind::ZFCMem { element, set } => vec![element, set],
        ExprKind::ZFCComprehension { domain, pred } => vec![domain, pred],
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(..)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => vec![],
    }
}

/// The node's own payload (everything but its `Arc` children).
fn node_payload(f: &mut Fields, e: &Expr) {
    match e.kind() {
        ExprKind::BVar(i) => f.u64(u64::from(*i)),
        ExprKind::FVar(id) => f.debug(id),
        ExprKind::Sort(l) => f.level(l),
        ExprKind::Const(n, ls) => {
            f.name(n);
            f.u64(ls.len() as u64);
            for l in ls.iter() {
                f.level(l);
            }
        }
        ExprKind::Lam(bd, ..) | ExprKind::Pi(bd, ..) => f.debug(&(bd.info, bd.mult)),
        ExprKind::Let(n, _, _, _, non_dep) => {
            f.name(n);
            f.u64(u64::from(*non_dep));
        }
        ExprKind::Lit(Literal::Nat(n)) => f.bytes(format!("nat:{n}").as_bytes()),
        ExprKind::Lit(Literal::String(s)) => f.bytes(format!("str:{s}").as_bytes()),
        ExprKind::Proj(n, i, _) => {
            f.name(n);
            f.u64(u64::from(*i));
        }
        ExprKind::MData(kv, _) => {
            f.u64(kv.len() as u64);
            for (k, v) in kv {
                f.name(k);
                match v {
                    MDataValue::Name(n) => f.name(n),
                    other => f.debug(other),
                }
            }
        }
        // Every other variant is identified by its tag and its children.
        _ => {}
    }
}

/// A fixed per-variant tag (not the compiler's discriminant, which is not a
/// stable identity across builds).
fn kind_tag(e: &Expr) -> &'static str {
    match e.kind() {
        ExprKind::BVar(_) => "bvar",
        ExprKind::FVar(_) => "fvar",
        ExprKind::Sort(_) => "sort",
        ExprKind::Const(..) => "const",
        ExprKind::App(..) => "app",
        ExprKind::Lam(..) => "lam",
        ExprKind::Pi(..) => "pi",
        ExprKind::Let(..) => "let",
        ExprKind::Lit(_) => "lit",
        ExprKind::Proj(..) => "proj",
        ExprKind::MData(..) => "mdata",
        ExprKind::SProp => "sprop",
        ExprKind::Squash(_) => "squash",
        ExprKind::CubicalInterval => "c_interval",
        ExprKind::CubicalI0 => "c_i0",
        ExprKind::CubicalI1 => "c_i1",
        ExprKind::CubicalPath { .. } => "c_path",
        ExprKind::CubicalPathLam { .. } => "c_path_lam",
        ExprKind::CubicalPathApp { .. } => "c_path_app",
        ExprKind::CubicalHComp { .. } => "c_hcomp",
        ExprKind::CubicalTransp { .. } => "c_transp",
        ExprKind::CubicalCoe { .. } => "c_coe",
        ExprKind::ZFCSet(set) => match set {
            ZFCSetExpr::Empty => "zfc_empty",
            ZFCSetExpr::Infinity => "zfc_infinity",
            ZFCSetExpr::Singleton(_) => "zfc_singleton",
            ZFCSetExpr::Union(_) => "zfc_union",
            ZFCSetExpr::PowerSet(_) => "zfc_powerset",
            ZFCSetExpr::Choice(_) => "zfc_choice",
            ZFCSetExpr::Pair(..) => "zfc_pair",
            ZFCSetExpr::Separation { .. } => "zfc_separation",
            ZFCSetExpr::Replacement { .. } => "zfc_replacement",
        },
        ExprKind::ZFCMem { .. } => "zfc_mem",
        ExprKind::ZFCComprehension { .. } => "zfc_comprehension",
    }
}

/// Bottom-up structural expression hasher with an address memo for SHARED
/// subterms (an `Arc` whose strong count exceeds one). The memo is valid
/// only while the environment it walks is borrowed, which the caller holds.
#[derive(Default)]
struct ExprDigester {
    memo: HashMap<usize, [u8; 16]>,
}

impl ExprDigester {
    fn digest(&mut self, root: &Expr) -> [u8; 16] {
        enum Task<'a> {
            Visit(&'a Expr, bool),
            Finish(&'a Expr, bool),
        }
        let mut stack = vec![Task::Visit(root, false)];
        let mut out: Vec<[u8; 16]> = Vec::new();
        while let Some(task) = stack.pop() {
            match task {
                Task::Visit(e, shared) => {
                    let key = std::ptr::from_ref(e) as usize;
                    if shared {
                        if let Some(d) = self.memo.get(&key) {
                            out.push(*d);
                            continue;
                        }
                    }
                    stack.push(Task::Finish(e, shared));
                    for child in children(e).into_iter().rev() {
                        stack.push(Task::Visit(child, Arc::strong_count(child) > 1));
                    }
                }
                Task::Finish(e, shared) => {
                    let n = children(e).len();
                    let mut f = Fields::new(kind_tag(e));
                    node_payload(&mut f, e);
                    let start = out.len().saturating_sub(n);
                    for d in out.drain(start..) {
                        f.bytes(&d);
                    }
                    let d = f.finish16();
                    if shared {
                        self.memo.insert(std::ptr::from_ref(e) as usize, d);
                    }
                    out.push(d);
                }
            }
        }
        out.pop().unwrap_or_default()
    }

    fn opt(&mut self, f: &mut Fields, e: Option<&Expr>) {
        match e {
            Some(e) => {
                let d = self.digest(e);
                f.bytes(&d);
            }
            None => f.bytes(b"none"),
        }
    }
}

// The per-entry encodings of the kernel's own records. Each DESTRUCTURES its
// record without `..`, so a field added to a record is a compile error here
// rather than a change these digests silently miss.

fn constant_row(ed: &mut ExprDigester, c: &super::ConstantInfo) -> [u8; 16] {
    let super::ConstantInfo {
        name,
        level_params,
        type_,
        value,
        is_reducible,
        reducibility,
        kind,
    } = c;
    let mut f = Fields::new("const");
    f.name(name);
    f.names(level_params);
    ed.opt(&mut f, Some(type_));
    ed.opt(&mut f, value.as_ref());
    f.debug(&(is_reducible, reducibility, kind));
    f.finish16()
}

fn inductive_row(ed: &mut ExprDigester, i: &crate::inductive::InductiveVal) -> [u8; 16] {
    let crate::inductive::InductiveVal {
        name,
        level_params,
        type_,
        num_params,
        num_indices,
        all_names,
        constructor_names,
        is_recursive,
        is_reflexive,
        is_large_elim,
        is_nested,
    } = i;
    let mut f = Fields::new("ind");
    f.name(name);
    f.names(level_params);
    ed.opt(&mut f, Some(type_));
    f.names(all_names);
    f.names(constructor_names);
    f.debug(&(num_params, num_indices, is_recursive, is_reflexive));
    f.debug(&(is_large_elim, is_nested));
    f.finish16()
}

fn constructor_row(ed: &mut ExprDigester, c: &crate::inductive::ConstructorVal) -> [u8; 16] {
    let crate::inductive::ConstructorVal {
        name,
        inductive_name,
        level_params,
        type_,
        num_params,
        num_fields,
        constructor_idx,
    } = c;
    let mut f = Fields::new("ctor");
    f.name(name);
    f.name(inductive_name);
    f.names(level_params);
    ed.opt(&mut f, Some(type_));
    f.debug(&(num_params, num_fields, constructor_idx));
    f.finish16()
}

fn recursor_row(ed: &mut ExprDigester, r: &crate::inductive::RecursorVal) -> [u8; 16] {
    let crate::inductive::RecursorVal {
        name,
        arg_order,
        level_params,
        type_,
        inductive_name,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        is_k,
    } = r;
    let mut f = Fields::new("rec");
    f.name(name);
    f.debug(arg_order);
    f.names(level_params);
    ed.opt(&mut f, Some(type_));
    f.name(inductive_name);
    f.debug(&(num_params, num_indices, num_motives, num_minors, is_k));
    f.u64(rules.len() as u64);
    for rule in rules {
        let crate::inductive::RecursorRule {
            constructor_name,
            num_fields,
            recursive_fields,
            rhs,
        } = rule;
        f.name(constructor_name);
        f.debug(&(num_fields, recursive_fields));
        ed.opt(&mut f, Some(rhs));
    }
    f.finish16()
}

fn quotient_row(ed: &mut ExprDigester, q: &crate::quot::QuotVal) -> [u8; 16] {
    let crate::quot::QuotVal {
        name,
        level_params,
        type_,
        kind,
    } = q;
    let mut f = Fields::new("quot");
    f.name(name);
    f.names(level_params);
    ed.opt(&mut f, Some(type_));
    f.debug(kind);
    f.finish16()
}

impl Environment {
    /// The digest of every KERNEL record this environment holds under `name`
    /// (its constant, inductive, constructor, recursor and quotient records,
    /// each in the encoding [`Self::content_digest`] uses), or `None` when it
    /// holds none. Two environments that agree on this digest for every name a
    /// checked declaration reaches (see [`Self::kernel_references`]) give that
    /// declaration the same kernel check: the kernel reads nothing else about
    /// another name. Trust keys its local kernel facts' dependencies on it.
    #[must_use]
    pub fn kernel_record_digest(&self, name: &Name) -> Option<[u8; 32]> {
        let mut ed = ExprDigester::default();
        let mut f = Fields::new("clean.kernel-record.v1");
        f.name(name);
        let mut any = false;
        let mut row = |f: &mut Fields, tag: &[u8], digest: Option<[u8; 16]>| match digest {
            Some(digest) => {
                any = true;
                f.bytes(tag);
                f.bytes(&digest);
            }
            None => f.bytes(b"-"),
        };
        let digest = self.constants.get(name).map(|c| constant_row(&mut ed, c));
        row(&mut f, b"const", digest);
        let digest = self.inductives.get(name).map(|i| inductive_row(&mut ed, i));
        row(&mut f, b"ind", digest);
        let digest = self
            .constructors
            .get(name)
            .map(|c| constructor_row(&mut ed, c));
        row(&mut f, b"ctor", digest);
        let digest = self.recursors.get(name).map(|r| recursor_row(&mut ed, r));
        row(&mut f, b"rec", digest);
        let digest = self.quotients.get(name).map(|q| quotient_row(&mut ed, q));
        row(&mut f, b"quot", digest);
        any.then(|| f.finish32())
    }

    /// Bind compiler metadata to a declaration's actual logical identity.
    /// Reducibility attributes are deliberately excluded: changing an inline
    /// policy must not turn another declaration's value into this one's body.
    /// This is metadata identity, not a proof or declaration admission check.
    #[must_use]
    pub fn compiler_declaration_digest(&self, name: &Name) -> Option<[u8; 32]> {
        self.get_const(name)
            .map(super::ConstantInfo::compiler_identity_digest)
    }

    /// Every other name the kernel records under `name` mention: the
    /// constants in its type and value and the structures their projections
    /// name, an inductive's family and constructors, a constructor's inductive,
    /// a recursor's inductive, constructors and rule right-hand sides. Sorted,
    /// without `name` itself.
    #[must_use]
    pub fn kernel_references(&self, name: &Name) -> Vec<Name> {
        let mut found = std::collections::HashSet::new();
        if let Some(c) = self.constants.get(name) {
            c.type_.collect_kernel_reads_into(&mut found);
            if let Some(value) = &c.value {
                value.collect_kernel_reads_into(&mut found);
            }
        }
        if let Some(i) = self.inductives.get(name) {
            i.type_.collect_kernel_reads_into(&mut found);
            found.extend(i.all_names.iter().cloned());
            found.extend(i.constructor_names.iter().cloned());
        }
        if let Some(c) = self.constructors.get(name) {
            c.type_.collect_kernel_reads_into(&mut found);
            found.insert(c.inductive_name.clone());
        }
        if let Some(r) = self.recursors.get(name) {
            r.type_.collect_kernel_reads_into(&mut found);
            found.insert(r.inductive_name.clone());
            for rule in &r.rules {
                found.insert(rule.constructor_name.clone());
                rule.rhs.collect_kernel_reads_into(&mut found);
            }
        }
        if let Some(q) = self.quotients.get(name) {
            q.type_.collect_kernel_reads_into(&mut found);
        }
        found.remove(name);
        let mut found: Vec<Name> = found.into_iter().collect();
        found.sort();
        found
    }

    /// SHA-256 of everything the environment records under `name` OUTSIDE its
    /// kernel records: the per-name tables the elaborator reads when a term
    /// names it, or names something under it. A structure's field names,
    /// defaults and parents (`p.f` elaborates to a projection whose index
    /// the field table decides, and the kernel type of a structure with two
    /// fields of one type does not say which is which); a class's instances;
    /// a constant's parameter names and binder kinds, and the binder names
    /// of the `∀` its value unfolds to (named arguments); its
    /// export alias, attributes, bindings and marks; whether it is a
    /// registered namespace. `None` when the environment records none of
    /// them.
    ///
    /// Each table is one entry of `ELABORATION_RECORD_TABLES`; a test pins
    /// that list against the local fact delta's typed components, so a table
    /// added to the environment is either digested here or excluded there
    /// with a reason. Trust folds this into the dependency digest of each
    /// name a local kernel fact reaches.
    #[must_use]
    pub fn elaboration_record_digest(&self, name: &Name) -> Option<[u8; 32]> {
        let mut ed = ExprDigester::default();
        let mut f = Fields::new("clean.elaboration-record.v1");
        f.name(name);
        let mut any = false;
        let mut row =
            |f: &mut Fields, table: &str, present: bool, write: &mut dyn FnMut(&mut Fields)| {
                f.bytes(table.as_bytes());
                f.u64(u64::from(present));
                if present {
                    any = true;
                    write(f);
                }
            };
        macro_rules! debug_rows {
            ($($table:ident),* $(,)?) => {$(
                let entry = self.$table.get(name);
                row(&mut f, stringify!($table), entry.is_some(), &mut |f| f.debug(&entry));
            )*};
        }
        debug_rows!(
            structure_fields,
            structure_parents,
            classes,
            instance_synth_orders,
            export_aliases,
            export_alias_others,
            extern_bindings,
            implemented_by,
            export_bindings,
            deprecated,
            derive_handlers,
            param_names,
            typed_param_names,
            param_binder_infos,
        );
        let binders = self.get_value_forall_binder_names(name);
        row(
            &mut f,
            "value_forall_binder_names",
            binders.is_some(),
            &mut |f| f.debug(&binders),
        );
        let compiled = super::csimp::recorded_body_rules(self, name);
        row(&mut f, "csimp_compiled", compiled.is_some(), &mut |f| {
            f.debug(&compiled)
        });
        let tags = super::ext_attr::registrations_of(self, name);
        row(&mut f, "attr_tags", !tags.is_empty(), &mut |f| {
            f.debug(&tags)
        });
        let codata = self.codata_origins.get(name);
        row(&mut f, "codata_origins", codata.is_some(), &mut |f| {
            f.debug(&codata)
        });
        let simp = self.simp_lemmas.get(name);
        row(&mut f, "simp_lemmas", simp.is_some(), &mut |f| {
            if let Some(info) = simp {
                f.debug(&(&info.name, &info.priority));
            }
        });
        let defaults = self.structure_field_defaults.get(name);
        let mut per_field: Vec<(String, [u8; 16])> = defaults
            .into_iter()
            .flatten()
            .map(|(field, e)| (key(field), ed.digest(e)))
            .collect();
        per_field.sort();
        row(
            &mut f,
            "structure_field_defaults",
            defaults.is_some(),
            &mut |f| {
                f.debug(&per_field);
            },
        );
        let insts = self.instances.get(name);
        let mut inst_rows = Vec::new();
        for inst in insts.into_iter().flatten() {
            // Registration order within a class is part of the table.
            let mut g = Fields::new("instance");
            g.name(&inst.name);
            g.name(&inst.class_name);
            g.u64(u64::from(inst.priority));
            ed.opt(&mut g, inst.type_.as_ref());
            ed.opt(&mut g, inst.value.as_ref());
            inst_rows.push(g.finish16());
        }
        row(&mut f, "instances", insts.is_some(), &mut |f| {
            f.u64(inst_rows.len() as u64);
            for inst in &inst_rows {
                f.bytes(inst);
            }
        });
        macro_rules! set_rows {
            ($($set:ident),* $(,)?) => {$(
                row(&mut f, stringify!($set), self.$set.contains(name), &mut |_| {});
            )*};
        }
        set_rows!(
            instance_names,
            declared_aesop_rule_sets,
            inline_hints,
            noinline_hints,
            always_inline_hints,
            macro_inline_hints,
            inline_if_reduce_hints,
            nospecialize_hints,
            specialize_hints,
            csimp_lemmas,
            congr_lemmas,
            ext_lemmas,
            refl_lemmas,
            symm_lemmas,
            coercion_decls,
            match_pattern_decls,
            init_fn_decls,
            default_instance_decls,
            private_decls,
            protected_decls,
            noncomputable_decls,
            partial_decls,
            unsafe_decls,
            local_instance_decls,
            registered_namespaces,
            staged_headers,
            codata_carriers,
        );
        any.then(|| f.finish32())
    }
}

/// The environment tables [`Environment::elaboration_record_digest`] reads,
/// by field name: the list `fact_delta`'s tests pin against the delta's typed
/// components.
#[cfg(test)]
pub(crate) const ELABORATION_RECORD_TABLES: &[&str] = &[
    "structure_fields",
    "structure_parents",
    "classes",
    "instance_synth_orders",
    "export_aliases",
    "export_alias_others",
    "extern_bindings",
    "implemented_by",
    "export_bindings",
    "deprecated",
    "derive_handlers",
    "param_names",
    "typed_param_names",
    "param_binder_infos",
    "value_forall_binder_names",
    "csimp_compiled",
    "attr_tags",
    "codata_origins",
    "simp_lemmas",
    "structure_field_defaults",
    "instances",
    "instance_names",
    "declared_aesop_rule_sets",
    "inline_hints",
    "noinline_hints",
    "always_inline_hints",
    "macro_inline_hints",
    "inline_if_reduce_hints",
    "nospecialize_hints",
    "specialize_hints",
    "csimp_lemmas",
    "congr_lemmas",
    "ext_lemmas",
    "refl_lemmas",
    "symm_lemmas",
    "coercion_decls",
    "match_pattern_decls",
    "init_fn_decls",
    "default_instance_decls",
    "private_decls",
    "protected_decls",
    "noncomputable_decls",
    "partial_decls",
    "unsafe_decls",
    "local_instance_decls",
    "registered_namespaces",
    "staged_headers",
    "codata_carriers",
];

fn section(name: &'static str, mut entries: Vec<(String, String)>) -> EnvDigestSection {
    entries.sort();
    let mut h = Sha256::new();
    for (k, d) in &entries {
        h.update(k.as_bytes());
        h.update(b"\t");
        h.update(d.as_bytes());
        h.update(b"\n");
    }
    EnvDigestSection {
        name,
        entries,
        sha256: hex(&h.finalize()),
    }
}

fn key(n: &Name) -> String {
    format!("{n}")
}

/// A section over a name-keyed map whose values need no expression hashing.
fn debug_section<'a, V: std::fmt::Debug + 'a>(
    name: &'static str,
    it: impl Iterator<Item = (&'a Name, V)>,
) -> EnvDigestSection {
    section(
        name,
        it.map(|(k, v)| {
            let mut f = Fields::new(name);
            f.name(k);
            f.debug(&v);
            (key(k), hex(&f.finish16()))
        })
        .collect(),
    )
}

/// A section over a set of names.
fn name_set_section<'a>(
    name: &'static str,
    it: impl Iterator<Item = &'a Name>,
) -> EnvDigestSection {
    debug_section(name, it.map(|n| (n, ())))
}

impl Environment {
    /// Compute the content digest of this environment. See the module docs
    /// for what is and is not covered.
    #[must_use]
    pub fn content_digest(&self) -> EnvContentDigest {
        let mut ed = ExprDigester::default();
        let mut sections = Vec::new();

        let mut rows = Vec::with_capacity(self.constants.len());
        for c in self.constants.values() {
            rows.push((key(&c.name), hex(&constant_row(&mut ed, c))));
        }
        sections.push(section("constants", rows));

        let mut rows = Vec::new();
        for i in self.inductives.values() {
            rows.push((key(&i.name), hex(&inductive_row(&mut ed, i))));
        }
        sections.push(section("inductives", rows));

        let mut rows = Vec::new();
        for c in self.constructors.values() {
            rows.push((key(&c.name), hex(&constructor_row(&mut ed, c))));
        }
        sections.push(section("constructors", rows));

        let mut rows = Vec::new();
        for r in self.recursors.values() {
            rows.push((key(&r.name), hex(&recursor_row(&mut ed, r))));
        }
        sections.push(section("recursors", rows));

        let mut rows = Vec::new();
        for q in self.quotients.values() {
            rows.push((key(&q.name), hex(&quotient_row(&mut ed, q))));
        }
        sections.push(section("quotients", rows));

        sections.push(debug_section(
            "constant_origins",
            self.constant_origins.iter(),
        ));
        sections.push(debug_section(
            "declaration_verification",
            self.declaration_verification.iter(),
        ));
        sections.push(debug_section(
            "value_forall_binder_names",
            self.value_binder_table().iter(),
        ));
        sections.push(debug_section(
            "structure_fields",
            self.structure_fields.iter(),
        ));
        sections.push(debug_section(
            "structure_parents",
            self.structure_parents.iter(),
        ));
        let mut rows = Vec::new();
        for (s, defaults) in &self.structure_field_defaults {
            let mut per_field: Vec<(String, String)> = defaults
                .iter()
                .map(|(field, e)| (key(field), hex(&ed.digest(e))))
                .collect();
            per_field.sort();
            let mut f = Fields::new("field_defaults");
            f.name(s);
            f.debug(&per_field);
            rows.push((key(s), hex(&f.finish16())));
        }
        sections.push(section("structure_field_defaults", rows));
        sections.push(debug_section("classes", self.classes.iter()));

        let mut rows = Vec::new();
        for (class, insts) in &self.instances {
            // Registration order within a class is part of the table.
            let mut f = Fields::new("instances");
            f.name(class);
            f.u64(insts.len() as u64);
            for inst in insts {
                f.name(&inst.name);
                f.name(&inst.class_name);
                f.u64(u64::from(inst.priority));
                ed.opt(&mut f, inst.type_.as_ref());
                ed.opt(&mut f, inst.value.as_ref());
            }
            rows.push((key(class), hex(&f.finish16())));
        }
        sections.push(section("instances", rows));
        sections.push(name_set_section(
            "instance_names",
            self.instance_names.iter(),
        ));
        sections.push(debug_section(
            "instance_synth_orders",
            self.instance_synth_orders.iter(),
        ));
        sections.push(debug_section(
            "simp_lemmas",
            self.simp_lemmas
                .iter()
                .map(|(n, info)| (n, (&info.name, &info.priority))),
        ));
        sections.push(debug_section("export_aliases", self.export_aliases.iter()));
        if !self.export_alias_others.is_empty() {
            sections.push(debug_section(
                "export_alias_others",
                self.export_alias_others.iter(),
            ));
        }
        sections.push(debug_section(
            "extern_bindings",
            self.extern_bindings.iter(),
        ));
        sections.push(debug_section("implemented_by", self.implemented_by.iter()));
        sections.push(debug_section(
            "export_bindings",
            self.export_bindings.iter(),
        ));
        sections.push(debug_section("deprecated", self.deprecated.iter()));
        sections.push(debug_section(
            "derive_handlers",
            self.derive_handlers.iter(),
        ));
        sections.push(debug_section("param_names", self.param_names.iter()));
        sections.push(debug_section(
            "typed_param_names",
            self.typed_param_names.iter(),
        ));
        sections.push(debug_section(
            "param_binder_infos",
            self.param_binder_infos.iter(),
        ));
        for (label, set) in [
            ("unsafe_decls", &self.unsafe_decls),
            ("partial_decls", &self.partial_decls),
            ("private_decls", &self.private_decls),
            ("protected_decls", &self.protected_decls),
            ("noncomputable_decls", &self.noncomputable_decls),
            ("inline_hints", &self.inline_hints),
            ("noinline_hints", &self.noinline_hints),
            ("always_inline_hints", &self.always_inline_hints),
            ("macro_inline_hints", &self.macro_inline_hints),
            ("inline_if_reduce_hints", &self.inline_if_reduce_hints),
            ("nospecialize_hints", &self.nospecialize_hints),
            ("specialize_hints", &self.specialize_hints),
            ("csimp_lemmas", &self.csimp_lemmas),
            ("congr_lemmas", &self.congr_lemmas),
            ("ext_lemmas", &self.ext_lemmas),
            ("refl_lemmas", &self.refl_lemmas),
            ("symm_lemmas", &self.symm_lemmas),
            ("coercion_decls", &self.coercion_decls),
            ("match_pattern_decls", &self.match_pattern_decls),
            ("init_fn_decls", &self.init_fn_decls),
            ("default_instance_decls", &self.default_instance_decls),
            ("codata_carriers", &self.codata_carriers),
        ] {
            sections.push(name_set_section(label, set.iter()));
        }
        sections.push(section(
            "grind_lemmas",
            self.grind_lemmas
                .iter()
                .enumerate()
                .map(|(i, (n, kind))| {
                    let mut f = Fields::new("grind");
                    f.name(n);
                    f.debug(kind);
                    (format!("{i:08}"), hex(&f.finish16()))
                })
                .collect(),
        ));
        sections.push(name_set_section(
            "native_reducer_names",
            self.native_reducers.keys(),
        ));

        let mut rows = Vec::new();
        for (ext, st) in self.persistent_extensions.states() {
            let mut f = Fields::new("persistent_ext");
            f.name(ext);
            f.u64(st.imported_entries.len() as u64);
            for (idx, module) in st.imported_entries.iter().enumerate() {
                f.u64(idx as u64);
                f.u64(module.len() as u64);
                for entry in module {
                    f.name(&entry.name);
                    f.debug(&entry.data);
                }
            }
            f.bytes(&st.state);
            rows.push((key(ext), hex(&f.finish16())));
        }
        sections.push(section("persistent_extensions", rows));

        let mut rows = Vec::new();
        for (ext, entries) in self.export_extension_states() {
            let mut lines: Vec<String> = entries
                .iter()
                .map(|e| format!("{}\t{:?}", e.name, e.data))
                .collect();
            lines.sort();
            let mut f = Fields::new("typed_ext");
            f.name(&ext);
            f.debug(&lines);
            rows.push((key(&ext), hex(&f.finish16())));
        }
        sections.push(section("typed_extension_exports", rows));

        let mut options: Vec<(String, String)> = self
            .options
            .iter()
            .map(|(k, v)| (k.clone(), format!("{v:?}")))
            .collect();
        options.sort();
        let mut f = Fields::new("scalars");
        f.debug(&self.mode);
        f.debug(&self.kernel_theory);
        f.debug(&self.lean_level_profile);
        f.debug(&(
            self.cumulative,
            self.suppress_lossy_structure_stubs,
            self.quot_init,
        ));
        f.debug(&options);
        f.debug(&(
            self.aesop_rules.safe_rules.len(),
            self.aesop_rules.unsafe_rules.len(),
            self.aesop_rules.norm_rules.len(),
            self.aesop_rule_sets.len(),
            self.declared_aesop_rule_sets.len(),
            self.codata_origins.len(),
        ));
        sections.push(section(
            "scalars",
            vec![("all".to_string(), f.finish_hex())],
        ));

        let mut total = Sha256::new();
        for s in &sections {
            total.update(format!("{} {} {}\n", s.name, s.entries.len(), s.sha256).as_bytes());
        }
        EnvContentDigest {
            sections,
            total: hex(&total.finalize()),
        }
    }
}

#[cfg(test)]
#[path = "content_digest_tests.rs"]
mod tests;

impl super::ConstantInfo {
    /// A compiler identity fingerprint, not evidence that this declaration is
    /// well typed or executable. Mutable reducibility attributes are excluded.
    #[must_use]
    pub fn compiler_identity_digest(&self) -> [u8; 32] {
        let mut ed = ExprDigester::default();
        let mut f = Fields::new("clean.compiler-declaration.v1");
        f.name(&self.name);
        f.names(&self.level_params);
        f.debug(&self.kind);
        ed.opt(&mut f, Some(&self.type_));
        ed.opt(&mut f, self.value.as_ref());
        f.finish32()
    }
}
