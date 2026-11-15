// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dependency-closed Merkle fingerprints of declarations, for the
//! extension-binding gate (see `super::extension_binding`).

use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::expr::{Expr, ExprKind, Literal};
use clean_kernel::level::Level;
use clean_kernel::name::{Name, NameInner};
use std::collections::{BTreeSet, HashMap};

/// How an `MData` wrapper enters a term's hash.
///
/// A wrapper is ERASED (hashed as its body) where every kernel judgment that
/// reads the term reads through it, and KEPT where one does not. The kernel's
/// judgments over an ordinary constant's type and value are transparent to
/// `MData`: `whnf` steps to the body (`tc/whnf.rs`), inference infers the body
/// (`tc/infer.rs`), definitional equality strips it on either side at every
/// level (`tc/def_eq/mod.rs`, `quick_is_def_eq`), instantiation and lifting
/// rebuild it around the substituted body (`expr/subst.rs`), and the
/// native-fold authority already digests it as its body
/// (`env/native_fold_digest.rs`). So two such terms that differ only in
/// annotations have one meaning, and they bind as one
/// (`fingerprint_mdata_lean_tests.rs` measures that, judgment by judgment, on
/// the v4.30.0-rc2 keys whose own values carry `MData`, and
/// `extension_binding_mdata_tests.rs` pins the binding controls).
///
/// A family's `add_inductive_core` input is read SYNTACTICALLY by admission:
/// the constructor telescope (`count_pi_args`, `get_return_type`), a field's
/// recursiveness (`env/inductive_recursor.rs`,
/// `field_is_eliminably_recursive`, through `head_beta_spine`, which contracts
/// β-redexes and does not step through `MData`) and the strict occurrence check
/// (`inductive/strict.rs`, `check_valid_ind_app`). Lean's admission whnfs a
/// field before it classifies it, so it reads through `MData` there, and
/// Clean's does not. A wrapper in a family input can therefore change what is
/// admitted, so a family's input is hashed with its wrappers, as before.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Annotations {
    /// An ordinary constant's type or value: `MData` hashes as its body.
    Erased,
    /// A family's inductive and constructor types: `MData` is hashed.
    Kept,
}

/// Dependency-closed Merkle fingerprints of declarations in one environment.
///
/// `fp(c) = H(kind, name, universe params, type, [value if a definition or
/// opaque], for each constant d mentioned: (d, fp(d)))`, with a theorem's value
/// deliberately left out (any proof of the same statement is interchangeable),
/// and a family member mapped to its whole block's `add_inductive_core` input.
/// Binder names and binder info are not hashed; they do not affect typing.
/// `MData` wrappers are erased from an ordinary constant's type and value and
/// kept in a family's input ([`Annotations`]).
pub(super) struct Fingerprinter<'a> {
    env: &'a Environment,
    done: HashMap<Name, [u8; 32]>,
    in_progress: BTreeSet<Name>,
    expr_memo: HashMap<(*const ExprKind, Annotations), [u8; 32]>,
    /// How an ordinary constant's wrappers enter its hash:
    /// [`Annotations::Erased`], except under the test-only
    /// [`Self::keeping_annotations`].
    ordinary_annotations: Annotations,
}

impl<'a> Fingerprinter<'a> {
    pub(super) fn new(env: &'a Environment) -> Self {
        Self {
            env,
            done: HashMap::new(),
            in_progress: BTreeSet::new(),
            expr_memo: HashMap::new(),
            ordinary_annotations: Annotations::Erased,
        }
    }

    /// The fingerprint as it was before 2026-11-14: every wrapper hashed,
    /// in an ordinary constant too. Tests compare against it to show which
    /// keys the erasure moves, and that it moves no other.
    #[cfg(test)]
    pub(super) fn keeping_annotations(env: &'a Environment) -> Self {
        Self {
            ordinary_annotations: Annotations::Kept,
            ..Self::new(env)
        }
    }

    /// The canonical head of the family `name` belongs to, if any.
    fn family_head(&self, name: &Name) -> Option<Name> {
        let env = self.env;
        let ind = env.get_inductive(name).or_else(|| {
            env.get_constructor(name)
                .and_then(|c| env.get_inductive(&c.inductive_name))
                .or_else(|| {
                    env.get_recursor(name)
                        .and_then(|r| env.get_inductive(&r.inductive_name))
                })
        })?;
        Some(
            ind.all_names
                .iter()
                .filter(|n| env.get_inductive(n).is_some())
                .min()
                .cloned()
                .unwrap_or_else(|| ind.name.clone()),
        )
    }

    pub(super) fn constant(&mut self, name: &Name) -> [u8; 32] {
        let key = self.family_head(name).unwrap_or_else(|| name.clone());
        if let Some(d) = self.done.get(&key) {
            return *d;
        }
        if !self.in_progress.insert(key.clone()) {
            // A reference cycle between ordinary constants cannot be admitted
            // by the replay at all; hash it as such, deterministically.
            let mut h = blake3::Hasher::new();
            h.update(b"cycle\0");
            hash_name(&mut h, &key);
            return *h.finalize().as_bytes();
        }
        let digest = if self.env.get_inductive(&key).is_some() {
            self.family(&key)
        } else {
            self.ordinary(&key)
        };
        self.in_progress.remove(&key);
        self.done.insert(key, digest);
        digest
    }

    fn ordinary(&mut self, name: &Name) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        let env: &'a Environment = self.env;
        let Some(info) = env.get_const(name) else {
            h.update(b"absent\0");
            hash_name(&mut h, name);
            return *h.finalize().as_bytes();
        };
        h.update(b"const\0");
        hash_name(&mut h, name);
        h.update(match info.kind {
            ConstantKind::Definition => b"def",
            ConstantKind::Theorem => b"thm",
            ConstantKind::Opaque => b"opq",
            ConstantKind::Axiom => b"axm",
        });
        hash_names(&mut h, &info.level_params);
        let mut refs = BTreeSet::new();
        let mode = self.ordinary_annotations;
        let ty = self.expr(&info.type_, &mut refs, mode);
        h.update(&ty);
        let hashes_value = matches!(info.kind, ConstantKind::Definition | ConstantKind::Opaque);
        match (&info.value, hashes_value) {
            (Some(value), true) => {
                h.update(b"value");
                let v = self.expr(value, &mut refs, mode);
                h.update(&v);
            }
            _ => {
                h.update(b"novalue");
            }
        }
        refs.remove(name);
        self.mix_refs(&mut h, refs, &BTreeSet::new());
        *h.finalize().as_bytes()
    }

    fn family(&mut self, head: &Name) -> [u8; 32] {
        let env = self.env;
        let mut h = blake3::Hasher::new();
        h.update(b"family\0");
        let Some(head_val) = env.get_inductive(head) else {
            return *h.finalize().as_bytes();
        };
        let members: Vec<Name> = if head_val.all_names.is_empty() {
            vec![head_val.name.clone()]
        } else {
            head_val.all_names.clone()
        };
        hash_names(&mut h, &head_val.level_params);
        h.update(&head_val.num_params.to_le_bytes());
        let mut own: BTreeSet<Name> = BTreeSet::new();
        let mut refs = BTreeSet::new();
        for family in &members {
            own.insert(family.clone());
            h.update(b"type");
            hash_name(&mut h, family);
            let Some(ind) = env.get_inductive(family) else {
                h.update(b"missing");
                continue;
            };
            let t = self.expr(&ind.type_, &mut refs, Annotations::Kept);
            h.update(&t);
            h.update(&(ind.constructor_names.len() as u64).to_le_bytes());
            for ctor in &ind.constructor_names {
                own.insert(ctor.clone());
                h.update(b"ctor");
                hash_name(&mut h, ctor);
                match env.get_constructor(ctor) {
                    Some(c) => {
                        let ct = self.expr(&c.type_, &mut refs, Annotations::Kept);
                        h.update(&ct);
                    }
                    None => {
                        h.update(b"missing");
                    }
                }
            }
        }
        self.mix_refs(&mut h, refs, &own);
        *h.finalize().as_bytes()
    }

    fn mix_refs(&mut self, h: &mut blake3::Hasher, refs: BTreeSet<Name>, own: &BTreeSet<Name>) {
        for r in refs {
            if own.contains(&r) {
                continue;
            }
            let d = self.constant(&r);
            h.update(b"ref");
            hash_name(h, &r);
            h.update(&d);
        }
    }

    /// Structural hash of `e`, memoised per shared node; collects every
    /// constant and projection structure name `e` mentions into `refs`.
    /// Under [`Annotations::Erased`] an `MData` node's hash IS its body's, so
    /// a term and the same term with any wrappers added or removed hash
    /// alike; every other node, and the constants collected, are unchanged.
    ///
    /// The memo is keyed by node address and annotation mode, which is sound
    /// only because every node is borrowed from the environment for `'a` —
    /// the lifetime the signature demands — so no address can be freed and
    /// reused while this fingerprinter lives.
    fn expr(&mut self, e: &'a Expr, refs: &mut BTreeSet<Name>, mode: Annotations) -> [u8; 32] {
        // Iterative post-order: Lean core terms are deep DAGs.
        enum Step<'e> {
            Enter(&'e Expr),
            Exit(&'e Expr),
        }
        let e: &'a Expr = e;
        let mut stack = vec![Step::Enter(e)];
        let mut seen_refs: std::collections::HashSet<*const ExprKind> = Default::default();
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(x) => {
                    let key = x.kind() as *const ExprKind;
                    if seen_refs.insert(key) {
                        match x.kind() {
                            ExprKind::Const(n, _) => {
                                refs.insert(n.clone());
                            }
                            ExprKind::Proj(s, _, _) => {
                                refs.insert(s.clone());
                            }
                            _ => {}
                        }
                    }
                    if self.expr_memo.contains_key(&(key, mode)) {
                        // Still need its refs: walk children for refs only if
                        // this node was hashed in another declaration.
                        collect_refs(x, refs, &mut seen_refs);
                        continue;
                    }
                    stack.push(Step::Exit(x));
                    for child in children(x).into_iter().rev() {
                        stack.push(Step::Enter(child));
                    }
                }
                Step::Exit(x) => {
                    let key = x.kind() as *const ExprKind;
                    if self.expr_memo.contains_key(&(key, mode)) {
                        continue;
                    }
                    let digest = match (x.kind(), mode) {
                        // Transparent to every judgment that reads an
                        // ordinary constant: the wrapper is its body.
                        (ExprKind::MData(_, body), Annotations::Erased) => {
                            self.expr_memo[&(body.kind() as *const ExprKind, mode)]
                        }
                        _ => {
                            let mut h = blake3::Hasher::new();
                            node_payload(&mut h, x);
                            for child in children(x) {
                                h.update(&self.expr_memo[&(child.kind() as *const ExprKind, mode)]);
                            }
                            *h.finalize().as_bytes()
                        }
                    };
                    self.expr_memo.insert((key, mode), digest);
                }
            }
        }
        self.expr_memo[&(e.kind() as *const ExprKind, mode)]
    }
}

/// Constants and projection structures mentioned by `e` (used when `e`'s hash
/// is already memoised).
fn collect_refs(
    e: &Expr,
    refs: &mut BTreeSet<Name>,
    seen: &mut std::collections::HashSet<*const ExprKind>,
) {
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        let key = x.kind() as *const ExprKind;
        if !seen.insert(key) && !std::ptr::eq(x, e) {
            continue;
        }
        match x.kind() {
            ExprKind::Const(n, _) => {
                refs.insert(n.clone());
            }
            ExprKind::Proj(s, _, _) => {
                refs.insert(s.clone());
            }
            _ => {}
        }
        stack.extend(children(x));
    }
}

/// The immediate sub-expressions of `e`, in a fixed order. An `MData`
/// payload is never hashed; its body is, and under [`Annotations::Erased`]
/// the body's hash stands for the node.
fn children(e: &Expr) -> Vec<&Expr> {
    match e.kind() {
        ExprKind::App(f, a) => vec![f.as_ref(), a.as_ref()],
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => vec![t.as_ref(), b.as_ref()],
        ExprKind::Let(_, t, v, b, _) => vec![t.as_ref(), v.as_ref(), b.as_ref()],
        ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) | ExprKind::Squash(x) => vec![x.as_ref()],
        _ => Vec::new(),
    }
}

/// Everything about `e`'s own node that is not a child. An `MData` node
/// reaches this only under [`Annotations::Kept`].
fn node_payload(h: &mut blake3::Hasher, e: &Expr) {
    match e.kind() {
        ExprKind::BVar(i) => {
            h.update(b"B");
            h.update(&i.to_le_bytes());
        }
        ExprKind::Sort(l) => {
            h.update(b"S");
            hash_level(h, l);
        }
        ExprKind::Const(n, ls) => {
            h.update(b"C");
            hash_name(h, n);
            h.update(&(ls.len() as u64).to_le_bytes());
            for l in ls.iter() {
                hash_level(h, l);
            }
        }
        ExprKind::App(..) => {
            h.update(b"A");
        }
        ExprKind::Lam(..) => {
            h.update(b"L");
        }
        ExprKind::Pi(..) => {
            h.update(b"P");
        }
        ExprKind::Let(..) => {
            h.update(b"Z");
        }
        ExprKind::Lit(Literal::Nat(v)) => {
            h.update(b"N");
            h.update(v.to_string().as_bytes());
            h.update(b"\0");
        }
        ExprKind::Lit(Literal::String(s)) => {
            h.update(b"T");
            h.update(&(s.len() as u64).to_le_bytes());
            h.update(s.as_bytes());
        }
        ExprKind::Proj(s, i, _) => {
            h.update(b"J");
            hash_name(h, s);
            h.update(&i.to_le_bytes());
        }
        ExprKind::MData(..) => {
            h.update(b"M");
        }
        ExprKind::Squash(_) => {
            h.update(b"Q");
        }
        other => {
            // Free variables and the cubical/impredicative extension nodes: a
            // Lean declaration contains none; hash their full debug form so
            // two different ones never collide.
            h.update(b"X");
            h.update(format!("{other:?}").as_bytes());
        }
    }
}

fn hash_level(h: &mut blake3::Hasher, l: &Level) {
    match l {
        Level::Zero => {
            h.update(b"0");
        }
        Level::Succ(a) => {
            h.update(b"+");
            hash_level(h, a);
        }
        Level::Max(a, b) => {
            h.update(b"M");
            hash_level(h, a);
            hash_level(h, b);
        }
        Level::IMax(a, b) => {
            h.update(b"I");
            hash_level(h, a);
            hash_level(h, b);
        }
        Level::Param(n) => {
            h.update(b"p");
            hash_name(h, n);
        }
    }
}

fn hash_names(h: &mut blake3::Hasher, names: &[Name]) {
    h.update(&(names.len() as u64).to_le_bytes());
    for n in names {
        hash_name(h, n);
    }
}

/// Component-wise, so `A.«b.c»` and `A.b.c` never collide.
fn hash_name(h: &mut blake3::Hasher, n: &Name) {
    let mut comps: Vec<&NameInner> = Vec::new();
    let mut cur = n;
    loop {
        match cur.inner() {
            NameInner::Anon => break,
            inner @ NameInner::Str(p, _) | inner @ NameInner::Num(p, _) => {
                comps.push(inner);
                cur = p.as_ref();
            }
        }
    }
    h.update(&(comps.len() as u64).to_le_bytes());
    for c in comps.into_iter().rev() {
        match c {
            NameInner::Str(_, s) => {
                h.update(b"s");
                h.update(&(s.len() as u64).to_le_bytes());
                h.update(s.as_bytes());
            }
            NameInner::Num(_, k) => {
                h.update(b"n");
                h.update(&k.to_le_bytes());
            }
            NameInner::Anon => {}
        }
    }
}

#[cfg(test)]
#[path = "mixed_world_pin_capture.rs"]
mod mixed_world_pin_capture;

#[cfg(test)]
#[path = "mixed_world_retired_pin_tests.rs"]
mod mixed_world_retired_pin_tests;
