// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Foreign-kernel cross-check exporter (self-verification Front #3).
//!
//! Walks the LIVE `clean_verify::Specification` environment and mechanically
//! exports the dependency closure of chosen root theorems as a single
//! self-contained Lean 4 file, so Lean's kernel independently re-checks the
//! same elaborated terms Clean's kernel checked.
//!
//! Fidelity contract:
//! - Terms are printed from the ELABORATED kernel `Expr`s stored in the live
//!   spec environment (post-elaboration ground truth), never hand-copied.
//! - Every value-less constant in the closure is emitted as an explicit Lean
//!   `axiom`, so `#print axioms <root>` shows the census honestly.
//! - Inductive types are reconstructed from the environment's `InductiveVal`
//!   (parameters/indices split exactly as Clean's kernel recorded them), and
//!   Lean regenerates its own recursors from that same declaration.
//! - Anything that cannot be exported faithfully is SKIPPED with a reason and
//!   reported (partial-but-honest coverage), never weakened.
//!
//! Usage:
//!   cargo run --release -p clean-verify --bin lean_export -- \
//!       [--out FILE] [root ...]
//! Default roots: tc_infer_soundness, bootstrap_infer_sound,
//! whnf_terminates_well_typed_dependent.

mod emit;
mod printer;

use std::collections::{HashMap, HashSet};
use std::io::Write as _;

use clean_kernel::{Environment, Expr, ExprKind, Name};
use clean_verify::Specification;

/// How a closure entry is realized in the Lean export.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ItemKind {
    /// A real inductive block (emitted with its constructors).
    Inductive,
    /// Value-less constant: explicit Lean `axiom`.
    Axiom,
    /// Prop-typed valued constant: Lean `theorem`.
    Theorem,
    /// Non-Prop valued constant: Lean `noncomputable def`.
    Def,
    /// Quot/Quot.mk/Quot.lift/Quot.ind: kernel primitives with a computation
    /// rule, emitted as a visible adapter block onto Lean core's built-in
    /// quotient (an `axiom` cannot carry the computation rule). `Quot.sound`
    /// stays a plain `Axiom`.
    QuotShim,
}

/// The four computation-rule-bearing quotient primitives (NOT `Quot.sound`,
/// which is a genuine axiom in both kernels).
const QUOT_SHIM_NAMES: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

struct Item {
    name: Name,
    kind: ItemKind,
}

const DEFAULT_ROOTS: [&str; 5] = [
    "tc_infer_soundness",
    "bootstrap_infer_sound",
    "whnf_terminates_well_typed_dependent",
    // C4 / the crystal: the layer-1 -> layer-2 bridge's keystone rule, and the
    // witness that keeps it from being a true-but-empty statement. Under
    // `--all-spec` this list is ALSO the set of `#print axioms` audit roots —
    // the only way a foreign kernel gets to confirm the zero-axiom claim
    // instead of us confirming it ourselves.
    "impl_bridge_fvar",
    "impl_bridge_fvar_witness",
];

fn main() {
    // Deep elaborated proof terms need more than the default stack for the
    // recursive printer; run the real work on a big-stack thread.
    let handle = std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(run)
        .expect("spawn export thread");
    match handle.join() {
        Ok(()) => {}
        Err(_) => std::process::exit(1),
    }
}

fn run() {
    let mut out_path = String::from("CleanVerifyExport.lean");
    let mut roots: Vec<String> = Vec::new();
    let mut all_spec = false;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        if a == "--out" {
            match args.next() {
                Some(p) => out_path = p,
                None => {
                    eprintln!("--out requires a path");
                    std::process::exit(2);
                }
            }
        } else if a == "--all-spec" {
            all_spec = true;
        } else {
            roots.push(a);
        }
    }
    if roots.is_empty() && !all_spec {
        roots = DEFAULT_ROOTS.iter().map(|s| (*s).to_string()).collect();
    }

    eprintln!("[lean_export] building live Specification::new() ...");
    let spec = match Specification::new() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[lean_export] FATAL: Specification::new() failed: {e:?}");
            std::process::exit(1);
        }
    };
    let env = spec.env();
    eprintln!(
        "[lean_export] spec built: {} spec definitions",
        spec.definitions().len()
    );

    if all_spec {
        // Root at every registered spec definition, in sorted name order for
        // deterministic output. The flagship roots stay first so the footer's
        // #print axioms audits them.
        let mut names: Vec<String> = spec.definitions().keys().cloned().collect();
        names.sort();
        roots = DEFAULT_ROOTS.iter().map(|s| (*s).to_string()).collect();
        for n in names {
            if !roots.contains(&n) {
                roots.push(n);
            }
        }
    }

    let mut walker = Walker::new(env);
    for r in &roots {
        walker.visit_name(&Name::from_string(r));
    }

    // Only audit the flagship roots in the footer (an --all-spec run has
    // thousands of roots; #print axioms on each would drown the output).
    let audit_roots: Vec<String> = if all_spec {
        DEFAULT_ROOTS.iter().map(|s| (*s).to_string()).collect()
    } else {
        roots.clone()
    };
    let header_desc: Vec<String> = if all_spec {
        vec![format!("--all-spec ({} spec definitions)", roots.len())]
    } else {
        roots.clone()
    };

    // Inductives to emit as Lean `structure`s: every Proj target seen in the
    // walked closure that is structure-like (single ctor, no indices, not
    // nested/mutual). Non-structure-like Proj targets stay unprintable and
    // their dependents are skipped honestly.
    let structs: HashSet<String> = walker
        .proj_targets
        .iter()
        .filter(|n| {
            env.get_inductive(n).is_some_and(|iv| {
                iv.all_names.len() == 1
                    && !iv.is_nested
                    && iv.constructor_names.len() == 1
                    && iv.num_indices == 0
            })
        })
        .map(|n| n.to_string())
        .collect();

    // Emit, with skip-propagation: an item depending on an unexportable item
    // is itself unexportable (its Lean reference would dangle). The walk order
    // is topological, so one forward pass propagates fully.
    // The Quot family is no longer quarantined: Quot/mk/lift/ind are emitted
    // as an adapter block onto Lean core's built-in quotient (ItemKind::
    // QuotShim), so Lean's own kernel supplies the computation rule
    // `Quot.lift f h (Quot.mk r a) == f a` that an explicit `axiom` could not
    // carry; `Quot.sound` stays an explicit axiom.
    let mut lean = String::new();
    lean.push_str(&emit::header(&header_desc));
    let mut emitted: HashSet<String> = HashSet::new();
    let mut skipped: Vec<(String, String)> = std::mem::take(&mut walker.skipped);
    let mut failed: HashSet<Name> = HashSet::new();
    for item in &walker.order {
        let bad_dep = walker
            .deps
            .get(&item.name)
            .into_iter()
            .flatten()
            .find(|d| failed.contains(d));
        let result = match bad_dep {
            Some(d) => Err(format!("depends on skipped {d}")),
            None => emit::emit_item(env, item, &walker.renames, &structs),
        };
        match result {
            Ok(text) => {
                lean.push_str(&text);
                lean.push('\n');
                emitted.insert(item.name.to_string());
            }
            Err(reason) => {
                failed.insert(item.name.clone());
                skipped.push((item.name.to_string(), reason.clone()));
                lean.push_str(&format!("-- SKIPPED {}: {}\n\n", item.name, reason));
            }
        }
    }
    // Audit roots that survived; a dropped audit root would break #print axioms.
    let surviving_audit: Vec<String> = audit_roots
        .iter()
        .filter(|r| emitted.contains(r.as_str()))
        .cloned()
        .collect();
    for r in &audit_roots {
        if !surviving_audit.contains(r) {
            eprintln!("[lean_export] WARNING: audit root {r} was skipped");
        }
    }
    lean.push_str(&emit::footer(&surviving_audit, &walker.renames));

    if let Err(e) = std::fs::File::create(&out_path).and_then(|mut f| f.write_all(lean.as_bytes()))
    {
        eprintln!("[lean_export] FATAL: cannot write {out_path}: {e}");
        std::process::exit(1);
    }

    // Coverage report.
    let spec_names: HashSet<&str> = spec.definitions().keys().map(String::as_str).collect();
    let exported_spec = emitted
        .iter()
        .filter(|n| spec_names.contains(n.as_str()))
        .count();
    // Constructors/recursors of exported inductives are covered via the block.
    let mut covered_via_block = 0usize;
    for name in &spec_names {
        if emitted.contains(*name) {
            continue;
        }
        let n = Name::from_string(name);
        let parent = if let Some(cv) = env.get_constructor(&n) {
            Some(cv.inductive_name.to_string())
        } else {
            env.get_recursor(&n).map(|rv| rv.inductive_name.to_string())
        };
        if let Some(p) = parent {
            if emitted.contains(&p) {
                covered_via_block += 1;
            }
        }
    }
    eprintln!("\n[lean_export] ==== COVERAGE ====");
    if roots.len() > 10 {
        eprintln!("[lean_export] roots: {} names (--all-spec)", roots.len());
    } else {
        eprintln!("[lean_export] roots: {roots:?}");
    }
    eprintln!(
        "[lean_export] emitted {} Lean declarations ({} closure items)",
        emitted.len(),
        walker.order.len()
    );
    eprintln!(
        "[lean_export] spec-definition coverage: {} directly + {} via inductive blocks, of {} total spec definitions",
        exported_spec,
        covered_via_block,
        spec.definitions().len()
    );
    let axioms: Vec<&Item> = walker
        .order
        .iter()
        .filter(|i| i.kind == ItemKind::Axiom)
        .collect();
    eprintln!(
        "[lean_export] explicit axioms in export ({}):",
        axioms.len()
    );
    for a in &axioms {
        eprintln!("[lean_export]   axiom {}", a.name);
    }
    let shims: Vec<&Item> = walker
        .order
        .iter()
        .filter(|i| i.kind == ItemKind::QuotShim)
        .collect();
    if !shims.is_empty() {
        eprintln!(
            "[lean_export] Quot-family adapter defs onto Lean core's built-in quotient ({}):",
            shims.len()
        );
        for s in &shims {
            eprintln!("[lean_export]   quot-shim {}", s.name);
        }
        eprintln!(
            "[lean_export]   (Lean side additionally trusts Lean core's Quot/mk/lift/ind primitives + their computation rule; Lean's own Quot.sound is never referenced)"
        );
    }
    if !structs.is_empty() {
        let mut ss: Vec<&String> = structs.iter().collect();
        ss.sort();
        eprintln!(
            "[lean_export] Proj-target inductives emitted as Lean structures ({}): {}",
            ss.len(),
            ss.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
        );
    }
    if skipped.is_empty() {
        eprintln!("[lean_export] skipped: none");
    } else {
        eprintln!("[lean_export] SKIPPED ({}):", skipped.len());
        for (n, r) in &skipped {
            eprintln!("[lean_export]   {n}: {r}");
        }
    }
    if !walker.renames.is_empty() {
        eprintln!("[lean_export] renames (Lean-reserved name collisions):");
        for (k, v) in &walker.renames {
            eprintln!("[lean_export]   {k} -> {v}");
        }
    }
    eprintln!("[lean_export] wrote {out_path}");
}

/// Dependency-closure walker: DFS post-order emission so dependencies precede
/// dependents. Constructor/recursor references redirect to their inductive.
struct Walker<'e> {
    env: &'e Environment,
    done: HashSet<Name>,
    in_progress: HashSet<Name>,
    order: Vec<Item>,
    skipped: Vec<(String, String)>,
    /// Per-item dependency lists (owner-redirected, self excluded), for
    /// skip-propagation: a dependent of an unexportable item is unexportable.
    deps: HashMap<Name, Vec<Name>>,
    /// Clean-name -> Lean-name remaps for Lean auto-generated collisions.
    renames: HashMap<String, String>,
    /// Inductives that appear as `ExprKind::Proj` targets anywhere in the
    /// walked closure — candidates for Lean `structure` emission.
    proj_targets: HashSet<Name>,
}

/// Suffixes Lean auto-generates for every inductive; a Clean CONSTANT (not the
/// recursor itself) with such a name under an exported inductive must be
/// renamed to avoid colliding with Lean's auto-generated declaration.
const LEAN_AUTOGEN_SUFFIXES: [&str; 9] = [
    "rec",
    "recOn",
    "casesOn",
    "below",
    "brecOn",
    "ibelow",
    "binductionOn",
    "noConfusion",
    "noConfusionType",
];

impl<'e> Walker<'e> {
    fn new(env: &'e Environment) -> Self {
        Walker {
            env,
            done: HashSet::new(),
            in_progress: HashSet::new(),
            order: Vec::new(),
            skipped: Vec::new(),
            deps: HashMap::new(),
            renames: HashMap::new(),
            proj_targets: HashSet::new(),
        }
    }

    /// Resolve a referenced name to the item that must be emitted for it.
    fn owner_of(&self, name: &Name) -> Name {
        if let Some(cv) = self.env.get_constructor(name) {
            return cv.inductive_name.clone();
        }
        if let Some(rv) = self.env.get_recursor(name) {
            return rv.inductive_name.clone();
        }
        name.clone()
    }

    fn visit_name(&mut self, raw: &Name) {
        let name = self.owner_of(raw);
        if self.done.contains(&name) {
            return;
        }
        if self.in_progress.contains(&name) {
            // Cycle (should only happen for self-references already excluded).
            return;
        }
        self.in_progress.insert(name.clone());

        let (kind, dep_exprs) = self.classify(&name);
        let mut my_deps: Vec<Name> = Vec::new();
        for e in &dep_exprs {
            collect_proj_targets(e, &mut self.proj_targets);
            for dep in const_deps(e) {
                let owner = self.owner_of(&dep);
                if owner != name {
                    self.visit_name(&dep);
                    if !my_deps.contains(&owner) {
                        my_deps.push(owner);
                    }
                }
            }
        }
        self.deps.insert(name.clone(), my_deps);

        self.in_progress.remove(&name);
        self.done.insert(name.clone());
        self.maybe_record_rename(&name, &kind);
        self.order.push(Item { name, kind });
    }

    /// Classify a closure entry and gather the expressions whose constants are
    /// its dependencies.
    fn classify(&mut self, name: &Name) -> (ItemKind, Vec<Expr>) {
        if let Some(iv) = self.env.get_inductive(name) {
            let mut exprs = vec![iv.type_.clone()];
            for cn in &iv.constructor_names {
                if let Some(cv) = self.env.get_constructor(cn) {
                    exprs.push(cv.type_.clone());
                }
            }
            return (ItemKind::Inductive, exprs);
        }
        if let Some(ci) = self.env.get_const(name) {
            let mut exprs = vec![ci.type_.clone()];
            let kind = match &ci.value {
                None if QUOT_SHIM_NAMES.contains(&name.to_string().as_str()) => ItemKind::QuotShim,
                None => ItemKind::Axiom,
                Some(v) => {
                    exprs.push(v.clone());
                    if ci.kind == clean_kernel::ConstantKind::Theorem {
                        ItemKind::Theorem
                    } else {
                        ItemKind::Def
                    }
                }
            };
            return (kind, exprs);
        }
        // Unknown constant: emit nothing; record as skipped via a stub axiom
        // attempt in emit (which will fail with a reason).
        (ItemKind::Axiom, Vec::new())
    }

    /// If a plain constant's name collides with a Lean auto-generated name of
    /// an exported inductive, rename it (mechanically, at declaration and all
    /// reference sites).
    fn maybe_record_rename(&mut self, name: &Name, kind: &ItemKind) {
        if *kind == ItemKind::Inductive {
            return;
        }
        let s = name.to_string();
        if let Some((base, last)) = s.rsplit_once('.') {
            if LEAN_AUTOGEN_SUFFIXES.contains(&last)
                && self.env.get_inductive(&Name::from_string(base)).is_some()
            {
                self.renames
                    .insert(s.clone(), format!("{base}.{last}_clean"));
            }
        }
    }
}

/// Collect constant names referenced by an expression, in first-occurrence
/// (deterministic) order.
fn const_deps(e: &Expr) -> Vec<Name> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            ExprKind::Const(n, _) if seen.insert(n.clone()) => {
                out.push(n.clone());
            }
            ExprKind::App(f, a) => {
                stack.push(a);
                stack.push(f);
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                stack.push(b);
                stack.push(t);
            }
            ExprKind::Let(_, t, v, b, _) => {
                stack.push(b);
                stack.push(v);
                stack.push(t);
            }
            ExprKind::Proj(n, _, inner) => {
                if seen.insert(n.clone()) {
                    out.push(n.clone());
                }
                stack.push(inner);
            }
            ExprKind::MData(_, inner) => stack.push(inner),
            // A Nat literal prints in constructor normal form over the mirror
            // Nat, so it depends on the Nat inductive block.
            ExprKind::Lit(clean_kernel::Literal::Nat(_)) => {
                for c in ["Nat.zero", "Nat.succ"] {
                    let n = Name::from_string(c);
                    if seen.insert(n.clone()) {
                        out.push(n);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Collect inductive names appearing as `ExprKind::Proj` targets.
fn collect_proj_targets(e: &Expr, out: &mut HashSet<Name>) {
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            ExprKind::App(f, a) => {
                stack.push(a);
                stack.push(f);
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                stack.push(b);
                stack.push(t);
            }
            ExprKind::Let(_, t, v, b, _) => {
                stack.push(b);
                stack.push(v);
                stack.push(t);
            }
            ExprKind::Proj(n, _, inner) => {
                out.insert(n.clone());
                stack.push(inner);
            }
            ExprKind::MData(_, inner) => stack.push(inner),
            _ => {}
        }
    }
}
