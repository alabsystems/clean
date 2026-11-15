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
//! - Nat has an explicitly proved carrier correspondence. The two reflected
//!   comparisons additionally have a proved change of evaluation strategy;
//!   their original bodies and body-dependent proof terms are retained and
//!   checked before their theorem images are transported by equality.
//! - Anything that cannot be exported faithfully is SKIPPED with a reason,
//!   never weakened. Both Byte profiles refuse any skipped closure; explicitly requested
//!   roots in every profile must be present and exported. The ordinary Full
//!   default retains its historical partial-but-honest coverage report.
//!
//! Usage:
//!   scripts/self_verify_crosscheck.sh
//! Or run `lean_export [--eval-ir-byte-v1] [--out FILE] [--all-spec] [root ...]`.
//! Without a profile flag, the Full specification and audit roots are unchanged.
//! `lean_export --eval-ir-byte-v1 --out ByteV1.lean ir_byte_run_add_v1` exports
//! a live byte/world operational theorem; it does not assert source refinement.
//! `--eval-ir-byte-literal-v1` selects Full plus ByteV1 and the checked literal
//! observer adapter, not a native Rust representation or source-refinement proof.

mod audit_roots;
mod comparison_bridge;
mod emit;
mod printer;
mod profile;

use std::collections::{HashMap, HashSet};
use std::io::Write as _;

use clean_kernel::{Environment, Expr, ExprKind, Name};
use clean_verify::Specification;
use profile::{Command, ExportProfile, RootSelection};

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
    /// The `Nat` INDUCTIVE, emitted as the bridged-carrier block rather than
    /// as a plain mirror inductive.
    ///
    /// The block emits, in order: the spec's own Nat inductive and its three
    /// declared bodies VERBATIM under the name `NatSpec`; the `toCore`/`ofCore`
    /// maps and eight correspondence theorems proving the two are the same
    /// algebra (including `rec_agrees`, universe-polymorphic); and then
    /// `Nat`/`.zero`/`.succ`/`.rec`/`.add`/`.sub`/`.pred` as reducible aliases
    /// of Lean's own `Nat` family, which is what every OTHER exported
    /// declaration then sees.
    ///
    /// This is a bridge that is PROVED, not asserted -- which is what
    /// distinguishes it from a bare alias. A bare alias would let a garbage
    /// declared body ride along invisibly in both kernels; the correspondence
    /// theorems refuse it (an off-by-one `toCore` is rejected, and a
    /// wrongly-recursing `NatSpec.add` makes `add_agrees` unprovable).
    NatCarrier,
    /// `Nat.add` / `Nat.sub` / `Nat.pred`. Emitted as part of the carrier
    /// block, so the item itself contributes only a provenance comment.
    ///
    /// These are the three operations with correspondence proofs in the
    /// carrier block. The live spec declares further Nat operations, which
    /// remain ordinary exported definitions until separately bridged. Clean's
    /// kernel reduces these operations natively on literal `BigNat` operands,
    /// keyed by name; symbolic operands can still unfold their stored bodies.
    /// They must be aliased AS A SET:
    /// aliasing `sub` while keeping the spec's `pred` spelling breaks the
    /// spec's own `sub_succ_succ`, because Lean's `sub` unfolds to Lean's
    /// `pred`, which is not defeq to the spec's `Nat.rec` spelling. Measured.
    NatShim,
    /// Reflected comparison with its original body and a checked, guarded
    /// subtraction image. Ordinary Nat.sub is left intact.
    ComparisonBridge,
    /// Recheck the original comparison agreement proof and transport its
    /// result along the checked comparison equality.
    ComparisonAgreement,
}

/// The four computation-rule-bearing quotient primitives (NOT `Quot.sound`,
/// which is a genuine axiom in both kernels).
const QUOT_SHIM_NAMES: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

/// The three Nat operations currently bridged onto Lean's own, each with a
/// checked correspondence theorem. Aliased AS A SET -- see
/// `ItemKind::NatShim`.
const NAT_SHIM_NAMES: [&str; 3] = ["Nat.add", "Nat.sub", "Nat.pred"];

/// Every name the carrier block routes onto Lean's own `Nat` family. Disclosed
/// in the export summary: a bridge the reader cannot see is not a bridge, it is
/// a substitution.
const NAT_BRIDGED_DISCLOSURE: [&str; 8] = [
    "Nat",
    "Nat.zero",
    "Nat.succ",
    "Nat.rec",
    "Nat.casesOn",
    "Nat.add",
    "Nat.sub",
    "Nat.pred",
];

struct Item {
    name: Name,
    kind: ItemKind,
}

/// What `-h`/`--help` prints: the grammar `run` parses, nothing more.
const USAGE: &str = "\
usage: lean_export [--eval-ir-byte-v1 | --eval-ir-byte-literal-v1] [--out FILE] [--all-spec] [root ...]
  --eval-ir-byte-v1  select the checked byte/world EvalIR prelude (default: Full spec)
  --eval-ir-byte-literal-v1  select Full plus ByteV1 and the literal observer adapter
  --out FILE        the Lean file to write (default CleanVerifyExport.lean)
  --all-spec        root at every definition in the selected profile, defaults first
  root ...          explicit declaration roots; never discarded by --all-spec
  With no roots, use the selected profile's audit roots: inference/implementation-model
  bridges for Full; run, call/return, byte-memory and final-world laws for ByteV1.
  The joint profile combines Full and Byte audit roots with the literal adapter roots.
  Both Byte profiles refuse any skipped closure. Explicit roots must exist and be exported in every
  profile. Full without explicit roots retains its reported partial-export behavior.
  Exit 0 means an export was written, NOT that Lean has checked it. Exit 1 means the spec,
  required closure or output failed; exit 2 means a bad argument.
";

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
    let options = match profile::parse_args(std::env::args().skip(1)) {
        Ok(Command::Export(options)) => options,
        Ok(Command::Help) => {
            print!("{USAGE}");
            return;
        }
        Err(error) => {
            eprint!("lean_export: {error}\n{USAGE}");
            std::process::exit(2);
        }
    };
    let out_path = &options.out_path;
    let all_spec = options.all_spec;

    let constructor = options.profile.constructor_name();
    eprintln!("[lean_export] building live {constructor} ...");
    let built = match options.profile {
        ExportProfile::Full => Specification::new(),
        ExportProfile::EvalIrByteV1 => Specification::new_eval_ir_byte_prelude_spec_v1(),
        ExportProfile::EvalIrByteLiteralV1 => Specification::new_eval_ir_byte_literal_spec_v1(),
    };
    let spec = match built {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[lean_export] FATAL: {constructor} failed: {e:?}");
            std::process::exit(1);
        }
    };
    let env = spec.env();
    eprintln!(
        "[lean_export] spec built: {} spec definitions",
        spec.definitions().len()
    );

    let selection = options.select_roots(spec.definitions().keys().map(String::as_str));
    if let Err(error) = require_roots_present(env, &selection.required_roots) {
        eprintln!("[lean_export] FATAL: {error}");
        std::process::exit(1);
    }
    let roots = &selection.roots;

    let mut walker = Walker::new(env);
    for r in roots {
        walker.visit_name(&Name::from_string(r));
    }

    // Only audit the flagship roots in the footer (an --all-spec run has
    // thousands of roots; #print axioms on each would drown the output).
    let audit_roots = &selection.audit_roots;
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
    match options.profile {
        ExportProfile::Full => {}
        ExportProfile::EvalIrByteV1 => lean.push_str(
            "-- Profile: EvalIR ByteV1; operational laws, not source-refinement evidence.\n\n",
        ),
        ExportProfile::EvalIrByteLiteralV1 => lean.push_str(
            "-- Profile: Full + EvalIR ByteV1 + literal observer adapter; not native Rust representation or source-refinement evidence.\n\n",
        ),
    }
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
        .filter(|r| walker.root_was_emitted(r, &emitted))
        .cloned()
        .collect();
    for r in audit_roots {
        if !surviving_audit.contains(r) {
            eprintln!("[lean_export] WARNING: audit root {r} was skipped");
        }
    }
    if let Err(error) = require_export_coverage(&selection, &walker, &emitted, &skipped) {
        // Refuse before opening the output: an incomplete strict export must
        // not overwrite an existing file with a success-shaped partial one.
        eprintln!("[lean_export] FATAL: {error}");
        std::process::exit(1);
    }
    lean.push_str(&emit::footer(&surviving_audit, &walker.renames));

    if let Err(e) = std::fs::File::create(out_path).and_then(|mut f| f.write_all(lean.as_bytes())) {
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
    if all_spec {
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
    let nat_bridged = walker.order.iter().any(|i| i.kind == ItemKind::NatCarrier);
    if nat_bridged {
        eprintln!(
            "[lean_export] Nat carrier bridged onto Lean core's own Nat ({}):",
            NAT_BRIDGED_DISCLOSURE.len()
        );
        for n in NAT_BRIDGED_DISCLOSURE {
            eprintln!("[lean_export]   nat-shim {n}");
        }
        eprintln!(
            "[lean_export]   (the spec's OWN Nat inductive and its add/sub/pred bodies are still emitted VERBATIM as CleanVerify.NatSpec and still re-checked by Lean; toCore/ofCore + 8 correspondence theorems -- incl. rec_agrees -- prove the two are the same algebra, with no axiom)"
        );
        eprintln!(
            "[lean_export]   (so every OTHER declaration is re-checked with Lean's Nat substituted for Clean's: Lean re-checks the IMAGE of Clean's theorem under a proved isomorphism, not the theorem verbatim -- see SELF_VERIFICATION_CERTIFICATE.md section 4)"
        );
    }
    let comparisons: Vec<&Item> = walker
        .order
        .iter()
        .filter(|i| i.kind == ItemKind::ComparisonBridge)
        .collect();
    if !comparisons.is_empty() {
        eprintln!(
            "[lean_export] reflected comparisons with checked evaluation-strategy bridges ({}):",
            comparisons.len()
        );
        for item in comparisons {
            eprintln!("[lean_export]   comparison-bridge {}", item.name);
        }
        eprintln!(
            "[lean_export]   (original stored bodies and walk-agreement proof terms are retained under ReplayBridge, independently rechecked, and transported only by proved pointwise equalities; ordinary Nat.sub is unchanged)"
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

fn declaration_present(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
}

fn require_roots_present(env: &Environment, roots: &[String]) -> Result<(), String> {
    let missing: Vec<_> = roots
        .iter()
        .filter(|root| !declaration_present(env, &Name::from_string(root)))
        .collect();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "required roots are absent from the selected live profile: {missing:?}"
        ))
    }
}

fn require_export_coverage(
    selection: &RootSelection,
    walker: &Walker<'_>,
    emitted: &HashSet<String>,
    skipped: &[(String, String)],
) -> Result<(), String> {
    let missing: Vec<_> = selection
        .required_roots
        .iter()
        .filter(|root| !walker.root_was_emitted(root, emitted))
        .collect();
    if !missing.is_empty() {
        return Err(format!("required roots were not exported: {missing:?}"));
    }
    if selection.refuse_skipped_closure && !skipped.is_empty() {
        return Err(format!(
            "ByteV1 export has {} skipped closure entries (first eight): {:?}",
            skipped.len(),
            skipped.iter().take(8).collect::<Vec<_>>()
        ));
    }
    Ok(())
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

    fn root_was_emitted(&self, root: &str, emitted: &HashSet<String>) -> bool {
        let name = Name::from_string(root);
        // Constructors and recursors are emitted through their inductive
        // block, not as independent entries in `emitted`. An absent root is
        // never rescued merely by having an identically spelled parent.
        declaration_present(self.env, &name) && emitted.contains(&self.owner_of(&name).to_string())
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
            // `Nat` becomes the bridged-carrier block instead of a plain mirror
            // inductive. The spec's inductive is still emitted and still
            // independently re-checked -- positivity, universe and recursor --
            // under the name `NatSpec`; only the working carrier changes.
            if name.to_string() == "Nat" {
                return (ItemKind::NatCarrier, exprs);
            }
            return (ItemKind::Inductive, exprs);
        }
        if let Some(ci) = self.env.get_const(name) {
            let mut exprs = vec![ci.type_.clone()];
            let kind = match &ci.value {
                None if QUOT_SHIM_NAMES.contains(&name.to_string().as_str()) => ItemKind::QuotShim,
                None => ItemKind::Axiom,
                // The three bridged ops. The VALUE is deliberately not pushed:
                // the carrier block emits the spec's body verbatim as
                // `NatSpec.add`/`.sub`/`.pred` from the environment, so walking the
                // body here would chase dependencies into names that are not
                // emitted under those spellings. The TYPE is still walked,
                // which is what forces the carrier block to be ordered first.
                Some(_) if NAT_SHIM_NAMES.contains(&name.to_string().as_str()) => ItemKind::NatShim,
                Some(v) => {
                    exprs.push(v.clone());
                    if comparison_bridge::COMPARISONS.contains(&name.to_string().as_str()) {
                        ItemKind::ComparisonBridge
                    } else if comparison_bridge::AGREEMENTS.contains(&name.to_string().as_str()) {
                        ItemKind::ComparisonAgreement
                    } else if ci.kind == clean_kernel::ConstantKind::Theorem {
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
            // A Nat literal prints as a numeral over the bridged carrier,
            // so it depends on the Nat carrier block.
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
