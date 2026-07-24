// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Genuine kernel verification of Metamath theorems.
//!
//! Translates a parsed Metamath proof into a `clean_kernel` derivation term and
//! runs `Environment::add_decl` — so the Clean kernel itself certifies the proof
//! (true `KernelVerified`), not a trusted Rust replayer. Uses the embedding in
//! [`clean_kernel::metamath_reflect`]: symbols are interned `Nat`s, expressions
//! are `List Nat`, each `$a` assertion is a schematic axiom
//! `Π σ, MMThm(applySubst σ h_0) → … → MMThm(applySubst σ concl)`, and a theorem
//! is proved by a derivation term applying them; the kernel reduces `applySubst`
//! at each step to confirm the (substituted) hypotheses match.
//!
//! Scope: uncompressed AND compressed proofs. Reuse of earlier `$p` theorems is
//! SCHEMATIC (M11): each verified theorem is registered as the kernel constant
//! `mm.<label> : Π σ, …` and reused by APPLYING it at the call-site σ — no
//! proof-tree inlining — so terms stay small (this dissolved both the deep-term
//! perf wall and a cache-size `is_def_eq` false-negative that capped the old
//! inlining path at ~180). Full `set.mm`: **3,200 verified, 0 failed, ~72 s**
//! (3,128 propositional via the schematic path + the $d-bearing fragment now
//! reached through the M12 guarded ground path below).
//!
//! SOUNDNESS ($d) — M12. A `Π σ` (schematic) theorem claims to hold for ALL
//! substitutions, which is correct only when its whole proof is `$d`-FREE. A proof
//! that APPLIES a `$d`-bearing axiom (ax-5, …) is therefore ROUTED to the GROUND
//! guarded path (`verify_metamath_theorem_guarded`): the theorem's variables are
//! concrete distinct symbols (so its own `$d` holds trivially) and each
//! `$d`-axiom application carries `disjPair … = true` GUARD arrows that the kernel
//! discharges by reducing `disjPair` on the substituted ground forms — a
//! `$d`-violating instance reduces to `Bool.false` and is REJECTED. Ground
//! theorems are not schematically reusable, so they are NOT added to `cache`/
//! `sigs` (dependents reusing them stay skipped, never wrongly accepted). The
//! `$d`-free fragment still takes the fast schematic path. The variable universe
//! fed to `varsOf`/`disjPair` (every `$v`/`$f` variable) is the one soundness-
//! critical input — see `collect_var_universe`. See
//! `docs/METAMATH_KERNEL_VERIFICATION.md`.

use hashbrown::HashMap;

use clean_kernel::metamath_reflect::{
    register_metamath_assertions, verify_metamath_theorem, verify_metamath_theorem_guarded,
    verify_metamath_theorem_schematic, verify_metamath_theorem_schematic_dv, MMAssertion,
    MMProofTree,
};
use clean_kernel::Environment;

use super::ast::{
    CompressedProof, Database, Formula, Proof, ResolvedAssertion, ResolvedDatabase,
    ResolvedStatement,
};
use super::{resolve_database, MetamathError, MetamathResult};

/// Interns Metamath symbol strings to `Nat` codes (stable within one run).
#[derive(Default)]
struct Interner {
    map: HashMap<String, u64>,
    next: u64,
}

impl Interner {
    fn new() -> Self {
        // Start at 1 so 0 is never a valid symbol code.
        Self {
            map: HashMap::new(),
            next: 1,
        }
    }

    fn intern(&mut self, s: &str) -> u64 {
        if let Some(&c) = self.map.get(s) {
            return c;
        }
        let c = self.next;
        self.next += 1;
        self.map.insert(s.to_string(), c);
        c
    }

    /// Intern a formula as `[typecode, tokens…]`.
    fn form(&mut self, f: &Formula) -> Vec<u64> {
        let mut v = Vec::with_capacity(f.tokens.len() + 1);
        v.push(self.intern(&f.typecode));
        for t in &f.tokens {
            v.push(self.intern(t));
        }
        v
    }

    fn tokens(&mut self, toks: &[String]) -> Vec<u64> {
        toks.iter().map(|t| self.intern(t)).collect()
    }

    /// Code → symbol map (for decoding diagnostics).
    fn reverse(&self) -> HashMap<u64, String> {
        self.map.iter().map(|(s, &c)| (c, s.clone())).collect()
    }
}

/// Decode the kernel's `TypeMismatch { expected, inferred }` by fully reducing
/// both `MMThm(form)` terms and decoding the `List Nat` to symbols.
fn decode_kernel_mismatch(
    env: &Environment,
    err: &clean_kernel::KernelEnvError,
    rev: &HashMap<u64, String>,
) -> Option<String> {
    use clean_kernel::{ExprKind, KernelEnvError, KernelTypeError, Literal};
    let KernelEnvError::TypeCheckFailed { source, .. } = err else {
        return None;
    };
    let KernelTypeError::TypeMismatch {
        expected, inferred, ..
    } = source
    else {
        return None;
    };
    let tc = clean_kernel::tc::TypeChecker::new(env);

    // `MMThm(form)` → decode `form` (a `List Nat`) by repeated whnf.
    let mmthm_form = |e: &clean_kernel::Expr| -> Option<Vec<u64>> {
        let w = tc.whnf(e);
        let ExprKind::App(_mmthm, form) = w.kind() else {
            return None;
        };
        let mut out = Vec::new();
        let mut cur = (**form).clone();
        loop {
            let lw = tc.whnf(&cur);
            let args: Vec<&clean_kernel::Expr> = lw.get_app_args().iter().copied().collect();
            // List.cons.{0} α head tail  → args = [α, head, tail]
            if args.len() == 3 {
                if let ExprKind::Lit(Literal::Nat(n)) = tc.whnf(args[1]).kind() {
                    out.push(n.to_u64().unwrap_or(0));
                    cur = args[2].clone();
                    continue;
                }
            }
            break; // List.nil or unrecognized
        }
        Some(out)
    };

    let dec = |e: &clean_kernel::Expr| match mmthm_form(e) {
        Some(codes) => decode(&codes, rev),
        None => "<non-MMThm>".to_string(),
    };
    // A FRESH `TypeChecker` finds the SAME two terms def-equal — confirming the
    // add_decl rejection is in-flight-state-dependent, not a property of the
    // terms (they also `whnf`-reduce to identical forms, above).
    let standalone_def_eq = tc.is_def_eq(expected, inferred);
    Some(format!(
        "forms_equal={} standalone_is_def_eq={standalone_def_eq} (add_decl rejected in-flight)",
        dec(expected) == dec(inferred)
    ))
}

/// Decode an interned form back to a readable symbol string.
fn decode(form: &[u64], rev: &HashMap<u64, String>) -> String {
    form.iter()
        .map(|c| rev.get(c).cloned().unwrap_or_else(|| format!("?{c}")))
        .collect::<Vec<_>>()
        .join(" ")
}

/// First mismatch found by the Rust re-checker.
struct RecheckErr {
    assertion: String,
    hyp_idx: usize,
    expected: Vec<u64>,
    got: Vec<u64>,
}

impl RecheckErr {
    fn decode(&self, rev: &HashMap<u64, String>) -> String {
        if self.hyp_idx == usize::MAX {
            return format!("unknown assertion {}", self.assertion);
        }
        format!(
            "MISMATCH applying {} hyp#{}: expected [{}] got [{}]",
            self.assertion,
            self.hyp_idx,
            decode(&self.expected, rev),
            decode(&self.got, rev)
        )
    }
}

/// Replay an [`MMProofTree`] against the axiom signatures (mirroring the kernel)
/// and return the form it proves, or the first hypothesis mismatch.
fn recheck(
    tree: &MMProofTree,
    axioms: &HashMap<String, (Vec<Vec<u64>>, Vec<u64>)>,
    hyp_forms: &[Vec<u64>],
) -> Result<Vec<u64>, RecheckErr> {
    match tree {
        MMProofTree::Hyp(j) => Ok(hyp_forms.get(*j).cloned().unwrap_or_default()),
        MMProofTree::Apply {
            assertion,
            subst,
            args,
        } => {
            let Some((ax_hyps, ax_concl)) = axioms.get(assertion) else {
                return Err(RecheckErr {
                    assertion: assertion.clone(),
                    hyp_idx: usize::MAX,
                    expected: vec![],
                    got: vec![],
                });
            };
            if args.len() != ax_hyps.len() {
                return Err(RecheckErr {
                    assertion: format!(
                        "{assertion} ARITY {} args vs {} hyps",
                        args.len(),
                        ax_hyps.len()
                    ),
                    hyp_idx: usize::MAX,
                    expected: vec![],
                    got: vec![],
                });
            }
            // Detect a duplicate-key subst: the kernel's subst_fn is a nested
            // iteList (FIRST match wins), so a duplicate key with a different
            // value would make the kernel disagree with a last-wins HashMap.
            let mut seen: HashMap<u64, &Vec<u64>> = HashMap::new();
            for (v, r) in subst {
                if let Some(prev) = seen.get(v) {
                    if *prev != r {
                        return Err(RecheckErr {
                            assertion: format!("{assertion} DUP-KEY var={v}"),
                            hyp_idx: usize::MAX,
                            expected: (*prev).clone(),
                            got: r.clone(),
                        });
                    }
                } else {
                    seen.insert(*v, r);
                }
            }
            for (i, (arg, hyp)) in args.iter().zip(ax_hyps.iter()).enumerate() {
                let expected = apply_first(subst, hyp);
                let got = recheck(arg, axioms, hyp_forms)?;
                if got != expected {
                    return Err(RecheckErr {
                        assertion: assertion.clone(),
                        hyp_idx: i,
                        expected,
                        got,
                    });
                }
            }
            Ok(apply_first(subst, ax_concl))
        }
    }
}

/// The kernel constant name for a Metamath label. `Name::from_string` splits on
/// `.`, so a dotted Metamath label (`pm2.1`) would become a HIERARCHICAL kernel
/// name `[mm, pm2, 1]` and collide with the namespace of sibling labels
/// (`Duplicate declaration`). Sanitize `.` to `_` so every Metamath label maps to
/// a single flat kernel-name component. (Metamath labels are unique, so the
/// sanitized names stay unique: `_` is not otherwise produced here.)
fn kernel_name(label: &str) -> String {
    format!("mm.{}", label.replace('.', "_"))
}

/// Outcome of attempting to kernel-verify one theorem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelVerifyOutcome {
    /// The Clean kernel accepted the derivation.
    Verified,
    /// The kernel rejected the derivation (with the error rendered).
    Rejected(String),
    /// Skipped (e.g. a compressed proof, or a step reusing a `$p` theorem).
    Skipped(String),
}

/// Kernel-verify a single `$p` theorem from `db` by its label.
///
/// Runs the whole-database verifier (so any earlier `$p` theorems this one reuses
/// are verified and cached first) and returns the outcome for `label`.
///
/// # Errors
/// Returns an error if the database fails to resolve or the label is not a
/// provable assertion.
pub fn kernel_verify_theorem(db: &Database, label: &str) -> MetamathResult<KernelVerifyOutcome> {
    let report = kernel_verify_database(db)?;
    if report.verified.iter().any(|l| l == label) {
        return Ok(KernelVerifyOutcome::Verified);
    }
    if let Some((_, e)) = report.failed.iter().find(|(l, _)| l == label) {
        return Ok(KernelVerifyOutcome::Rejected(e.clone()));
    }
    if let Some((_, r)) = report.skipped.iter().find(|(l, _)| l == label) {
        return Ok(KernelVerifyOutcome::Skipped(r.clone()));
    }
    Err(MetamathError::InvalidStatement(format!(
        "{label} is not a provable ($p) assertion in the database"
    )))
}

/// Collect the COMPLETE variable-code universe from the raw database: every
/// `$v`-declared variable and every `$f`-float variable (union), interned. This is
/// the soundness-critical input to `varsOf`/`disjPair`: it must contain every
/// variable (a missing one would let `varsOf` under-count and a `$d` violation slip
/// through). Constants ($c) are deliberately excluded — over-inclusion would only
/// cause spurious rejections, but under-inclusion would be unsound.
fn collect_var_universe(db: &Database, interner: &mut Interner) -> Vec<u64> {
    fn walk(stmts: &[super::ast::Statement], names: &mut std::collections::BTreeSet<String>) {
        use super::ast::Statement;
        for s in stmts {
            match s {
                Statement::Variables(vs) => names.extend(vs.iter().cloned()),
                Statement::Floating { variable, .. } => {
                    names.insert(variable.clone());
                }
                Statement::Block(inner) => walk(inner, names),
                _ => {}
            }
        }
    }
    let mut names = std::collections::BTreeSet::new();
    walk(&db.statements, &mut names);
    names.iter().map(|n| interner.intern(n)).collect()
}

/// Build an axiom for every `$f` floating hypothesis: `mm.<flabel> : MMThm([tc,
/// var])` (registered schematically as `Π σ, MMThm(applySubst σ [tc,var])`, so
/// applying it at the identity substitution yields the ground typing). This lets a
/// proof reference a NON-mandatory (dummy/work) variable's float: the variable's
/// typing is supplied by its `$f` axiom rather than by a theorem hypothesis. Sound:
/// a `$f` is a Metamath grammar postulate (the variable's typecode), exactly the
/// kind of `$a`-level fact the embedding already trusts (AXIOMATIZED/trust-gated).
/// Freshness of a dummy is enforced separately by the M12 `$d` guards.
fn float_axiom_assertions(db: &Database, interner: &mut Interner) -> Vec<MMAssertion> {
    fn walk(
        stmts: &[super::ast::Statement],
        out: &mut Vec<(String, String, String)>,
        seen: &mut std::collections::BTreeSet<String>,
    ) {
        use super::ast::Statement;
        for s in stmts {
            match s {
                Statement::Floating {
                    label,
                    typecode,
                    variable,
                } if seen.insert(label.clone()) => {
                    out.push((label.clone(), typecode.clone(), variable.clone()));
                }
                Statement::Block(inner) => walk(inner, out, seen),
                _ => {}
            }
        }
    }
    let mut floats = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    walk(&db.statements, &mut floats, &mut seen);
    floats
        .into_iter()
        .map(|(label, tc, var)| MMAssertion {
            name: kernel_name(&label),
            float_hyps: vec![],
            essential_hyps: vec![],
            conclusion: vec![interner.intern(&tc), interner.intern(&var)],
            disjoints: vec![],
            var_universe: vec![],
        })
        .collect()
}

/// Build `MMAssertion`s for all `$a` axioms in the resolved database. `var_universe`
/// is the database's full variable-code set (for the `$d` guards on `$d`-bearing
/// axioms).
fn axiom_assertions(
    resolved: &ResolvedDatabase,
    interner: &mut Interner,
    var_universe: &[u64],
) -> Vec<MMAssertion> {
    let mut out = Vec::new();
    for stmt in &resolved.statements {
        if let ResolvedStatement::Assertion(a) = stmt {
            if a.kind != "axiom" {
                continue;
            }
            out.push(MMAssertion {
                name: kernel_name(&a.label),
                float_hyps: a
                    .mandatory_floats
                    .iter()
                    .map(|h| (interner.intern(&h.typecode), interner.intern(&h.variable)))
                    .collect(),
                essential_hyps: a
                    .essential_hyps
                    .iter()
                    .map(|h| interner.form(&h.formula))
                    .collect(),
                conclusion: interner.form(&a.formula),
                // Full $d frame of the axiom (e.g. ax-5's $d x ph), interned — each
                // pair becomes a `disjPair … = true` guard arrow (M12).
                disjoints: a
                    .disjoints
                    .iter()
                    .map(|(x, y)| (interner.intern(x), interner.intern(y)))
                    .collect(),
                var_universe: var_universe.to_vec(),
            });
        }
    }
    out
}

/// Maximum node count of an (inlined) proof tree before we skip it — guards
/// against the exponential blow-up of fully expanding deeply-reused proofs.
const MAX_TREE_SIZE: usize = 2_000_000;

/// A previously-verified `$p` theorem's axiom-expanded proof tree. Its `Hyp(j)`
/// nodes reference its own frame (mandatory floats then essentials, by index).
#[derive(Clone)]
struct CachedTheorem {
    tree: MMProofTree,
}

/// Report from kernel-verifying a whole database.
#[derive(Debug, Default, Clone)]
pub struct KernelVerifyReport {
    /// Labels the Clean kernel verified.
    pub verified: Vec<String>,
    /// `(label, error)` for theorems the kernel rejected.
    pub failed: Vec<(String, String)>,
    /// `(label, reason)` for theorems skipped (compressed proof, oversized
    /// inlined tree, or a dependency that itself did not verify).
    pub skipped: Vec<(String, String)>,
    /// `(kernel_name, type_expr, value_expr)` for each verified theorem — the
    /// material a Mathverse exporter needs to write a `KernelVerified` shard.
    pub verified_exprs: Vec<(String, clean_kernel::Expr, clean_kernel::Expr)>,
}

/// Kernel-verify every `$p` theorem in `db`, in source order, reusing earlier
/// theorems by inlining their (already-verified) axiom-expanded proof trees.
///
/// # Errors
/// Returns an error only if the database fails to resolve or the axiom
/// signature cannot be registered; per-theorem outcomes are recorded in the
/// returned [`KernelVerifyReport`].
pub fn kernel_verify_database(db: &Database) -> MetamathResult<KernelVerifyReport> {
    kernel_verify_database_prefix(db, usize::MAX)
}

/// Like [`kernel_verify_database_prefix`] but skips collecting `verified_exprs`
/// (the per-theorem `(name, type, value)` tuples used only for Mathverse export).
/// At full set.mm scale those clones roughly DOUBLE peak memory and trigger
/// macOS memory-compressor thrashing; a pure verify/count pass (e.g. `mm_kverify`)
/// does not use them, so this keeps memory bounded. Verified counts are identical.
pub fn kernel_verify_database_prefix_count_only(
    db: &Database,
    max_provables: usize,
) -> MetamathResult<KernelVerifyReport> {
    kernel_verify_database_prefix_impl(db, max_provables, CollectMode::CountOnly, TwoPass::Single)
}

/// TWO-PASS PARALLEL kernel verification of a `range` of `$p` theorem indices.
///
/// This is the parallelizable verifier. It runs both passes against a SINGLE
/// freshly-built environment:
///
/// * PASS 1 (cheap, sequential) registers EVERY `$p` theorem's schematic TYPE as
///   an axiom (no proof check) so the full dependency-type environment exists.
/// * PASS 2 (expensive) re-verifies the PROOFS of only the theorems whose
///   0-based provable ordinal lies in `range`, against the pass-1 axiom
///   environment. Each `range` is independent, so N workers can each call this
///   with a disjoint `range` and the driver unions their `report.verified`.
///
/// Only theorems verified in pass-2 appear in `report.verified` — see
/// [`set_mm_axiom_only`](clean_kernel::set_mm_axiom_only) for the soundness
/// argument. `range` is over PROVABLE ORDINALS (the 0-based index of a theorem
/// among `$p` statements in source order), matching the `mm_verify_range` binary.
/// Passing `range = 0..max_provables` re-verifies the whole prefix and is the
/// COUNT-EQUIVALENCE check against the sequential verifier.
///
/// # Errors
/// See [`kernel_verify_database`].
pub fn kernel_verify_two_pass_range(
    db: &Database,
    range: std::ops::Range<usize>,
    max_provables: usize,
) -> MetamathResult<KernelVerifyReport> {
    kernel_verify_database_prefix_impl(
        db,
        max_provables,
        CollectMode::CountOnly,
        TwoPass::Pass2(range),
    )
}

/// PASS-1-ONLY schematic TYPE export for an ALREADY-VERIFIED label set.
///
/// This is the type-collection half of the two-pass verifier WITHOUT any proof
/// re-checking. It runs ONLY PASS 1 (`set_mm_axiom_only` ON): each `$p` theorem's
/// schematic TYPE is registered as an axiom — the SAME construction
/// (`build_tree` + `verify_metamath_theorem_schematic*`) the real verifier uses,
/// so the registered `mm.<label>` type is byte-identical to what a checked run
/// would produce. For each theorem whose Metamath label is in `wanted`, the sink
/// receives `(label, kernel_name, type_expr)` read straight from
/// `env.get_const(mm.<label>).type_` — the kernel's own registered type.
///
/// Memory is bounded by RANGE-SCOPING pass-1 to `wanted` ∪ its transitive
/// `$p`-dependency closure (the deps needed to schematically BUILD each wanted
/// theorem's type); everything outside that closure is skipped. Chunk `wanted`
/// (call this repeatedly with disjoint subsets) to bound the resident set further.
///
/// SOUNDNESS: this registers types WITHOUT checking proofs and is therefore NOT a
/// verifier — the caller MUST pass a `wanted` set whose proofs were ALREADY
/// kernel-checked elsewhere (the two-pass `mm_verify_range` + `mm_gate` gated
/// set). A `$p` theorem's schematic type is determined entirely by its statement
/// (its frame + conclusion), not by its proof, so reading it after pass-1 yields
/// exactly the type the checked verifier registered for that already-proven
/// theorem. The sink fires only for labels in `wanted`; no other label is emitted.
///
/// # Errors
/// See [`kernel_verify_database`].
pub fn kernel_verify_pass1_types(
    db: &Database,
    max_provables: usize,
    wanted: &hashbrown::HashSet<String>,
    sink: &mut dyn FnMut(&str, &str, &clean_kernel::Expr),
) -> MetamathResult<KernelVerifyReport> {
    kernel_verify_database_prefix_impl(
        db,
        max_provables,
        CollectMode::Pass1Types { wanted, sink },
        TwoPass::Pass1Types(wanted.clone()),
    )
}

/// Like [`kernel_verify_database`] but stops after attempting `max_provables`
/// theorems (in source order). Useful for bounded coverage experiments on large
/// databases, where the proof-inlining strategy's worst-case blow-up makes a
/// full pass impractical.
///
/// # Errors
/// See [`kernel_verify_database`].
pub fn kernel_verify_database_prefix(
    db: &Database,
    max_provables: usize,
) -> MetamathResult<KernelVerifyReport> {
    kernel_verify_database_prefix_impl(db, max_provables, CollectMode::Collect, TwoPass::Single)
}

/// Like [`kernel_verify_database_prefix`] but STREAMS each verified theorem's
/// `(name, type, value)` to `sink` and then immediately drops the proof value
/// (`forget_value`), so values never accumulate. This keeps peak memory bounded
/// for full-corpus Mathverse export (the alternative — collecting all ~25-30k
/// values into `verified_exprs` while the Environment also retains them — needs
/// ~90 GB). `report.verified_exprs` stays empty; the sink is the consumer.
/// Verified/failed/skipped counts are identical to [`kernel_verify_database_prefix`].
///
/// # Errors
/// See [`kernel_verify_database`].
pub fn kernel_verify_database_prefix_streaming(
    db: &Database,
    max_provables: usize,
    sink: &mut dyn FnMut(&str, &clean_kernel::Expr, &clean_kernel::Expr),
) -> MetamathResult<KernelVerifyReport> {
    kernel_verify_database_prefix_impl(
        db,
        max_provables,
        CollectMode::Stream(sink),
        TwoPass::Single,
    )
}

/// Which pass of the TWO-PASS PARALLEL verifier a run is executing.
///
/// The two-pass design splits verification so the expensive proof checks
/// parallelize across disjoint theorem ranges:
///
/// * [`Single`](TwoPass::Single) — the original sequential verifier. Each `$p`
///   theorem is proof-checked in source order and its checked schematic type is
///   reused (`cache`/`sigs`) by later theorems.
/// * [`Pass1`](TwoPass::Pass1) — CHEAP. Registers EVERY `$p` theorem's schematic
///   TYPE as an AXIOM (via the thread-local `set_mm_axiom_only` flag), WITHOUT
///   type-checking the proof. Builds the full type environment pass-2 reuses.
///   `report.verified` stays EMPTY (pass-1 proves nothing). No type-forgetting:
///   the whole environment must survive for pass-2.
/// * [`Pass2`](TwoPass::Pass2) — EXPENSIVE, PARALLELIZABLE. For each `$p`
///   theorem whose index is in `range`, `forget_decl`s its pass-1 axiom and runs
///   the normal verify path (re-adds it as a `Theorem`, type-checking the proof
///   against the pass-1 axiom environment). Adds to `report.verified` ONLY on a
///   checked success. Theorems OUTSIDE `range` are left as pass-1 axioms (they
///   are the dependency types this worker's range reuses).
#[derive(Clone)]
enum TwoPass {
    /// Original single sequential pass (proof-check + schematic reuse).
    Single,
    /// Pass 1: register every theorem's type as an axiom, no proof check.
    Pass1,
    /// Pass 2: re-verify proofs for theorem indices in this statement-index range.
    Pass2(std::ops::Range<usize>),
    /// Pass-1-only TYPE export (no proof check) for an ALREADY-VERIFIED label set.
    /// Identical to [`Pass1`](TwoPass::Pass1) (registers types as axioms, runs ONE
    /// phase, `report.verified` stays empty) but RANGE-SCOPED to the wanted labels
    /// ∪ their transitive `$p`-dependency closure so a chunked caller bounds memory.
    /// Drives [`kernel_verify_pass1_types`]; the wanted set is also the export
    /// filter (see [`CollectMode::Pass1Types`]).
    Pass1Types(hashbrown::HashSet<String>),
}

/// Disposition of each verified theorem's `(type, value)` — see the match in
/// [`kernel_verify_database_prefix_impl`].
enum CollectMode<'a> {
    /// Drop the value (`forget_value`); `verified_exprs` stays empty.
    CountOnly,
    /// Accumulate `(name, type, value)` clones into `report.verified_exprs`.
    Collect,
    /// Hand `(name, type, value)` to the sink, then drop the value.
    Stream(&'a mut dyn FnMut(&str, &clean_kernel::Expr, &clean_kernel::Expr)),
    /// PASS-1 TYPE EXPORT (no proof value exists in this mode — it is an axiom-only
    /// pass). For each registered theorem whose Metamath label is in `wanted`, hand
    /// `(label, kernel_name, type_expr)` to the sink. The wanted filter makes the
    /// export emit ONLY the already-verified labels the caller asked for, never a
    /// dependency that was merely registered to build a wanted type. Drives
    /// [`kernel_verify_pass1_types`].
    Pass1Types {
        wanted: &'a hashbrown::HashSet<String>,
        sink: &'a mut dyn FnMut(&str, &str, &clean_kernel::Expr),
    },
}

/// Implementation of the prefix verifier. `mode` controls what happens to each
/// verified theorem's `(name, type, value)` — see [`CollectMode`].
fn kernel_verify_database_prefix_impl(
    db: &Database,
    max_provables: usize,
    mut mode: CollectMode<'_>,
    two_pass: TwoPass,
) -> MetamathResult<KernelVerifyReport> {
    // For the TWO-PASS verifier, run PASS 1 first: register every `$p` theorem's
    // schematic TYPE as an axiom (no proof check) so the dependency-type
    // environment exists, then fall through to PASS 2 below which re-verifies the
    // proofs in `range`. PASS 1 shares the SAME loop body (so the type shapes /
    // schematic routing are byte-identical to what pass-2 expects) but the
    // axiom-only flag turns each theorem's `add_decl` into an axiom registration.
    // The whole environment is handed to pass-2 via the returned `Environment`.
    // We thread the pass through to the loop rather than re-running it twice over
    // the same `env`, because pass-1's accumulated `sigs`/`guards`/`cache`/dummy
    // state is exactly what pass-2 needs and rebuilding it identically is what
    // guarantees count-equivalence.
    let resolved = resolve_database(db)?;
    let mut interner = Interner::new();
    let var_universe = collect_var_universe(db, &mut interner);
    let assertions = axiom_assertions(&resolved, &mut interner, &var_universe);

    // Every `$f` float becomes a GROUND axiom `mm.<flabel> : Π σ, MMThm([tc,var])`
    // (σ ignored — see `register_float_axiom`) so a proof can reference a DUMMY/work
    // variable's typing (the "non-mandatory floating hyp" case) without a theorem
    // hypothesis. A proof that uses one is routed to the ground path (the schematic
    // `Π σ` form would let σ corrupt the dummy). Registered separately from the
    // schematic `$a` axioms because their body must NOT be `applySubst σ`.
    let float_assertions = float_axiom_assertions(db, &mut interner);
    let mut float_axiom_names: hashbrown::HashSet<String> =
        float_assertions.iter().map(|a| a.name.clone()).collect();

    // M12/M13: number of `$d` guard arrows each guarded assertion carries — used to
    // discharge them (one ground `Eq.refl Bool.true` each) on the ground path.
    // Axioms carry one arrow per pair (register_metamath_assertions); verified
    // `$d`-theorems carry BOTH orders (verify_metamath_theorem_schematic_dv), so
    // they are added below with `2 * pairs` as they verify.
    let mut guard_counts: std::collections::HashMap<String, usize> = assertions
        .iter()
        .filter(|a| !a.disjoints.is_empty())
        .map(|a| (a.name.clone(), a.disjoints.len()))
        .collect();
    // M13: `$d` pair frame of each guarded assertion, in the order its guard arrows
    // were registered — axioms one order; verified `$d`-theorems BOTH orders. Drives
    // the schematic discharge. Grows as `$d`-bearing theorems verify schematically.
    let mut guards: hashbrown::HashMap<String, Vec<(u64, u64)>> = assertions
        .iter()
        .filter(|a| !a.disjoints.is_empty())
        .map(|a| (a.name.clone(), a.disjoints.clone()))
        .collect();

    // Axiom signatures (interned) for the diagnostic re-checker: name ->
    // (mandatory hyp forms [floats as [tc,var] then essentials], conclusion).
    // Float-axioms are included (empty hyps, ground `[tc,var]` conclusion) — applied
    // with an empty substitution they re-check to exactly `[tc,var]`.
    let mut axiom_map: HashMap<String, (Vec<Vec<u64>>, Vec<u64>)> = assertions
        .iter()
        .chain(float_assertions.iter())
        .map(|a| {
            let mut hyps: Vec<Vec<u64>> = a.float_hyps.iter().map(|&(tc, v)| vec![tc, v]).collect();
            hyps.extend(a.essential_hyps.iter().cloned());
            (a.name.clone(), (hyps, a.conclusion.clone()))
        })
        .collect();

    let mut env = Environment::new();
    // Disable the kernel heartbeat (fuel) limit: a deeply-inlined Metamath
    // derivation reduces `applySubst` over large forms many times, which exceeds
    // the default 2M-tick budget and shows up as a spurious type mismatch. Sound
    // — `maxHeartbeats=0` only removes a resource cap, not a correctness check.
    //
    // `CLEAN_MM_HEARTBEAT=<N>` (N>0) re-imposes a per-theorem tick cap. This is
    // FAIL-CLOSED and fully SOUND: a proof that exceeds N ticks raises
    // HeartbeatExceeded, which the verify loop records as a SKIP — the theorem is
    // never marked verified, so no false `KernelVerified` can result. The point is
    // throughput: pathological single-axiom proofs cost tens of minutes EACH and
    // stall a whole-corpus run; capping them skips that handful so the verifiable
    // BULK ships, with the skipped slow proofs left as a known (recoverable) gap.
    let max_hb = std::env::var("CLEAN_MM_HEARTBEAT").unwrap_or_else(|_| "0".to_string());
    env.set_option("maxHeartbeats".to_string(), Some(max_hb));
    // TC cache policy: use the kernel's default (large, fast) cache for the common
    // case, and retry a FAILED theorem with the cache bounded to 0 (see the verify
    // loop below). A large cache can retain an `Expr`-keyed reduction/inference
    // entry across a binder-context boundary in very deep proof terms and return
    // it for a structurally-equal-but-context-distinct read — a def-eq
    // FALSE-negative that wrongly rejects valid deep proofs (e.g. `simprim`).
    // Bounding the cache is sound (it can never accept an unequal pair). Keeping
    // the fast cache by default and only retrying on failure preserves throughput.
    // `CLEAN_MM_CACHE` overrides the fast-path cap. See
    // docs/METAMATH_KERNEL_VERIFICATION.md.
    if let Ok(c) = std::env::var("CLEAN_MM_CACHE") {
        env.set_option("tcMaxCacheEntries".to_string(), Some(c));
    }
    register_metamath_assertions(&mut env, &assertions)
        .map_err(|e| MetamathError::InvalidStatement(format!("register assertions: {e}")))?;
    // Register the `$f` float-axioms with their SOUND ground bodies.
    for fa in &float_assertions {
        clean_kernel::metamath_reflect::register_float_axiom(
            &mut env,
            &fa.name,
            fa.conclusion[0],
            fa.conclusion[1],
        )
        .map_err(|e| MetamathError::InvalidStatement(format!("register float axiom: {e}")))?;
    }

    // Signatures (hyp forms in Π-order, conclusion) of every reusable assertion —
    // the `$a` axioms now, plus each `$p` theorem as it verifies. Drives schematic
    // reuse: a proof step applies `mm.<label>` and the builder needs its shape.
    let mut sigs: HashMap<String, (Vec<Vec<u64>>, Vec<u64>)> = HashMap::new();
    for a in &assertions {
        let mut hf: Vec<Vec<u64>> = a.float_hyps.iter().map(|&(tc, v)| vec![tc, v]).collect();
        hf.extend(a.essential_hyps.iter().cloned());
        sigs.insert(a.name.clone(), (hf, a.conclusion.clone()));
    }
    // M13-dummy: the `$f` float-axioms also go in `sigs` (empty hyps, `[tc,var]`
    // conclusion) so the schematic builder recognises a dummy float leaf and reads
    // its `[tc, d]` to emit the σ-fixes-d cast.
    for fa in &float_assertions {
        sigs.insert(fa.name.clone(), (Vec::new(), fa.conclusion.clone()));
    }

    // M13-dummy: per verified theorem, its TRANSITIVE dummy frame (own work
    // variables ∪ those of every theorem it reuses). Drives the σ-fixes-d guards a
    // reusing theorem must carry + discharge. Grows as dummy theorems verify.
    let mut dummy_frames: hashbrown::HashMap<String, Vec<u64>> = hashbrown::HashMap::new();

    // SOUNDNESS GUARD ($d). A theorem is registered as `Π σ, …` — it claims to
    // hold for ALL substitutions. That is correct ONLY when the theorem and its
    // whole proof are `$d`-FREE. A `$d`-constrained theorem (predicate logic) does
    // NOT hold for every σ, and the predicate-logic axioms (ax-5, …) are sound
    // only under their `$d` side-conditions — which this encoding does not carry.
    // So: collect the `$a` axioms/definitions that bear `$d`; skip any theorem
    // that references one (via `build_tree`) or carries its own `$d`. This keeps
    // every verified theorem's closure `$d`-free, so the all-σ claim is sound.
    let mut tainted: hashbrown::HashSet<String> = hashbrown::HashSet::new();
    for stmt in &resolved.statements {
        if let ResolvedStatement::Assertion(a) = stmt {
            if a.kind == "axiom" && !a.disjoints.is_empty() {
                tainted.insert(kernel_name(&a.label));
            }
        }
    }
    // A proof needs the GROUND guarded path if it applies a `$d`-bearing axiom OR
    // references a non-mandatory (dummy) float-axiom — the schematic `Π σ` form
    // handles neither (σ would corrupt a dummy; the all-σ claim drops `$d`).
    let needs_ground: hashbrown::HashSet<String> =
        tainted.union(&float_axiom_names).cloned().collect();

    let mut cache: HashMap<String, CachedTheorem> = HashMap::new();
    let mut report = KernelVerifyReport::default();
    // M13-dummy: globally-fresh codes for per-proof dummy α-renaming. Base far above
    // any interned symbol code (set.mm has < 2^21 symbols) so a fresh dummy is `∉ vu`
    // and distinct from every real variable — see `rename_tree_dummies`.
    let mut fresh_dummy_ctr: u64 = 1u64 << 40;

    // Type-forgetting (peak-memory bound): pre-scan every provable's proof for the
    // LAST statement that cites each label, so that label's kernel type + importer
    // caches can be dropped the moment no later proof can reference it. Without this
    // the accumulating schematic `mm.<label>` types OOM a 24 GB host around ~N=4500
    // even with `forget_value` (which only drops proof VALUES, not the types kept
    // for reuse). SAFE: a too-eager drop can only make a later reuse fail (fewer
    // verified — caught by count-equivalence vs the un-forgotten run), NEVER a false
    // accept; `remove_constant` on an absent name is a no-op.
    let mut forget_at: std::collections::HashMap<usize, Vec<String>> =
        std::collections::HashMap::new();
    {
        let mut last_use: std::collections::HashMap<&str, usize> = std::collections::HashMap::new();
        for (i, stmt) in resolved.statements.iter().enumerate() {
            if let ResolvedStatement::Assertion(a) = stmt {
                if a.kind == "provable" {
                    match &a.proof {
                        Some(Proof::Uncompressed(ls)) => {
                            for l in ls {
                                last_use.insert(l.as_str(), i);
                            }
                        }
                        Some(Proof::Compressed(c)) => {
                            for l in &c.labels {
                                last_use.insert(l.as_str(), i);
                            }
                        }
                        None => {}
                    }
                }
            }
        }
        for (label, i) in last_use {
            forget_at.entry(i).or_default().push(label.to_string());
        }
    }

    // RANGE-SCOPED PASS-1 (peak-memory bound for a parallel `Pass2(range)` worker).
    //
    // A worker that proof-checks only the provables whose ordinal lies in `[a,b)`
    // does NOT need the full `[0,end)` type environment in memory. It needs only the
    // types its range actually REUSES: the `$p` theorems transitively cited by the
    // proofs of the in-range provables (the base `$a` axioms and `$f` floats are
    // always registered separately, before the phases). Without this scoping, PASS 1
    // accumulates EVERY `$p` type in `[0,end)` — so each parallel worker would hold
    // (almost) the whole type environment and OOM a 24 GB host on the full corpus.
    //
    // `reuse_set` = transitive closure, over the `$p`-theorem dependency graph, of
    // the labels cited by the in-range proofs (seeded ALSO with the in-range labels
    // themselves: an in-range theorem's own type is forgotten and rebuilt in pass-2,
    // but seeding it keeps the closure self-contained and is harmless). In PASS 1 we
    // register a `$p` theorem's type ONLY if its label is in `reuse_set`; everything
    // else is skipped, so pass-1's resident set is bounded by the deps `[a,b)` uses.
    //
    // SOUNDNESS: a `$p` type that a `[a,b)` proof actually needs but that is wrongly
    // omitted here → its `build_tree` reuse fails → that proof fails to type-check →
    // the theorem is SKIPPED (fail-closed) and the gate drops its dependents. NEVER a
    // false accept. So a mis-computed `reuse_set` can only LOSE verifications — which
    // the count-equivalence check against the sequential verifier catches. The
    // closure mirrors `mm_gate`'s `$p`-dependency edges, in the needed-by-range
    // direction. `Single`/`Pass1` modes set this to `None` (register everything).
    // `CLEAN_MM_NO_RANGE_SCOPE=1` disables range-scoping (PASS 1 registers EVERY
    // type, the original whole-prefix behavior). Kept as a kill-switch / A-B knob:
    // the optimization can only LOSE verifications if `reuse_set` is wrong, so being
    // able to fall back to the (slower, heavier) full registration without a rebuild
    // is a cheap safety valve.
    let range_scope_disabled = std::env::var("CLEAN_MM_NO_RANGE_SCOPE").is_ok();
    // Seed labels for the reuse-closure: an in-range ordinal's label (`Pass2`) or the
    // wanted labels (`Pass1Types`). `None` ⇒ no range-scoping (`Single`/`Pass1`, or
    // when disabled by the kill-switch). For `Pass1Types` the scope is ALWAYS applied
    // (its whole point is to register only the wanted closure); the kill-switch only
    // governs `Pass2`.
    let scope_request: Option<&TwoPass> = match &two_pass {
        TwoPass::Pass2(_) if !range_scope_disabled => Some(&two_pass),
        TwoPass::Pass1Types(_) => Some(&two_pass),
        _ => None,
    };
    let reuse_set: Option<hashbrown::HashSet<String>> = if let Some(req) = scope_request {
        // Per-provable `$p`-theorem dependency edges (cited labels that are
        // themselves provables) and the in-source-order provable labels (for the
        // ordinal → label seed). Built once from the resolved database.
        let mut provable: hashbrown::HashSet<&str> = hashbrown::HashSet::new();
        for stmt in &resolved.statements {
            if let ResolvedStatement::Assertion(a) = stmt {
                if a.kind == "provable" {
                    provable.insert(a.label.as_str());
                }
            }
        }
        let mut deps: hashbrown::HashMap<&str, Vec<&str>> = hashbrown::HashMap::new();
        let mut provable_order: Vec<&str> = Vec::new();
        for stmt in &resolved.statements {
            if let ResolvedStatement::Assertion(a) = stmt {
                if a.kind == "provable" {
                    provable_order.push(a.label.as_str());
                    let cited: &[String] = match &a.proof {
                        Some(Proof::Uncompressed(ls)) => ls,
                        Some(Proof::Compressed(c)) => &c.labels,
                        None => &[],
                    };
                    let d: Vec<&str> = cited
                        .iter()
                        .map(String::as_str)
                        .filter(|l| provable.contains(*l))
                        .collect();
                    deps.insert(a.label.as_str(), d);
                }
            }
        }
        // Seed the worklist: every in-range provable's label (`Pass2`) or every
        // wanted label that is a known provable (`Pass1Types`). Then transitively
        // close over `$p`-dependency edges. The `end` bound matches `max_provables`
        // (the prefix the pass traverses), so an ordinal beyond `provable_order`
        // simply contributes nothing.
        let mut keep: hashbrown::HashSet<String> = hashbrown::HashSet::new();
        let mut work: Vec<&str> = Vec::new();
        match req {
            TwoPass::Pass2(range) => {
                for ord in range.clone() {
                    if let Some(&label) = provable_order.get(ord) {
                        if keep.insert(label.to_string()) {
                            work.push(label);
                        }
                    }
                }
            }
            TwoPass::Pass1Types(wanted) => {
                // Seed with the wanted labels (interned against the provable set so a
                // stray non-provable label is dropped, never seeded). The closure adds
                // the `$p` deps needed to schematically build each wanted type.
                for &label in &provable_order {
                    if wanted.contains(label) && keep.insert(label.to_string()) {
                        work.push(label);
                    }
                }
            }
            _ => {}
        }
        while let Some(label) = work.pop() {
            if let Some(ds) = deps.get(label) {
                for &d in ds {
                    if keep.insert(d.to_string()) {
                        // `d` is a provable label (filtered above); recurse into its deps.
                        if let Some((&k, _)) = deps.get_key_value(d) {
                            work.push(k);
                        }
                    }
                }
            }
        }
        if std::env::var("CLEAN_MM_PROF").is_ok() {
            use std::io::Write;
            let _ = writeln!(
                std::io::stderr(),
                "PROF REUSE_SET keep={} (provables in prefix={})",
                keep.len(),
                provable_order.len()
            );
            let _ = std::io::stderr().flush();
        }
        Some(keep)
    } else {
        None
    };

    // TWO-PASS orchestration. `Single` → one traversal (the original behavior).
    // `Pass2(range)` → TWO traversals over the SAME `env`: PASS 1 registers every
    // theorem's TYPE as an axiom (flag ON, no proof check, no `verified` push, no
    // type-forgetting), building the dependency-type environment; PASS 2 (flag
    // OFF) re-verifies the PROOFS of theorems whose provable ordinal is in `range`
    // and adds them to `verified`. Provable ordinal = 0-based position among `$p`
    // statements in source order.
    let phases: Vec<TwoPass> = match &two_pass {
        TwoPass::Single => vec![TwoPass::Single],
        TwoPass::Pass1 => vec![TwoPass::Pass1],
        TwoPass::Pass2(r) => vec![TwoPass::Pass1, TwoPass::Pass2(r.clone())],
        // Pass-1-only TYPE export: a SINGLE pass-1 phase (axiom-only, no proof
        // check). No second phase — the caller only wants the types.
        TwoPass::Pass1Types(w) => vec![TwoPass::Pass1Types(w.clone())],
    };

    // RAII reset + G1 SENTINEL: `MmAxiomOnlyGuard::enter()` marks this thread as
    // being inside the sanctioned two-pass for the whole function body. It (a)
    // establishes the `mm_two_pass_active()` sentinel that AUTHORIZES the kernel's
    // axiom-only proof-drop fast path (without it, `add_decl` under the flag fails
    // closed to `AxiomOnlyMisuse` — Pillar-1 gap G1), and (b) clears the axiom-only
    // flag on ANY exit from this function (including `?` early-returns inside the
    // loop), so the flag can never leak ON into later checked work on this thread.
    // SOUNDNESS: sound precisely because PASS-2 re-verifies every in-range proof and
    // only PASS-2-verified theorems are exported; the guard is the token proving we
    // are in that regime.
    let _axiom_only_reset = clean_kernel::MmAxiomOnlyGuard::enter();

    for phase in &phases {
        // `Pass1Types` is an axiom-only TYPE pass, so it shares the pass-1 path:
        // flag ON (no proof check), no `verified` push, and NO type-forgetting (the
        // bounded reuse-closure is its memory bound). It differs only in the export
        // sink firing for wanted labels (handled in the `Ok(())` arm below).
        let in_pass1 = matches!(phase, TwoPass::Pass1 | TwoPass::Pass1Types(_));
        let mut pass2_range: Option<std::ops::Range<usize>> = match phase {
            TwoPass::Pass2(r) => Some(r.clone()),
            _ => None,
        };
        // #4 SHARED-ENV PARALLELISM: PASS-1 (above phases) built the env ONCE in this
        // process. For the PASS-2 phase, fork `MM_PARALLEL` workers that each verify a
        // disjoint sub-range on a COPY-ON-WRITE share of that env — PASS-1 is physically
        // shared (1×env, not N×env), only each worker's private PASS-2 forget/re-add
        // mutations are COW-copied. SOUNDNESS: each worker runs the IDENTICAL PASS-2 over
        // the IDENTICAL post-PASS-1 env, just over its sub-range, so the union of verified
        // labels is byte-identical to the sequential run; a crashed/failed worker simply
        // drops its sub-range's labels (fail-closed) — never a false accept. Single-threaded
        // at this point, so fork() is safe.
        let mut child_sink: Option<std::path::PathBuf> = None;
        let mut stride: Option<(usize, usize)> = None;
        // #4 fork-COW parallel PASS-2 is Unix-only: it relies on `fork()`, which has no
        // Windows equivalent. On non-Unix targets this dispatch is compiled out and PASS-2
        // runs sequentially over the full range (`child_sink`/`stride` stay `None`) — the
        // identical checked path and verified set as `MM_PARALLEL=1`, just single-process.
        // See `fork_parallel_pass2` / `ParallelRole` / `mm_parallel_workers` (all `#[cfg(unix)]`).
        #[cfg(unix)]
        if !in_pass1 {
            if let Some(full) = pass2_range.clone() {
                let workers = mm_parallel_workers().min(full.end.saturating_sub(full.start));
                if workers > 1 {
                    match fork_parallel_pass2(&full, workers, &mut report) {
                        ParallelRole::Child {
                            idx,
                            n,
                            full: fr,
                            sink,
                        } => {
                            pass2_range = Some(fr);
                            stride = Some((idx, n));
                            child_sink = Some(sink);
                        }
                        ParallelRole::ParentDone => {
                            // children produced this phase's labels; skip the parent body.
                            clean_kernel::set_mm_axiom_only(false);
                            continue;
                        }
                    }
                }
            }
        }
        // PASS 1 globally enables axiom-only mode for THIS thread: every theorem's
        // `add_decl` registers its type as an axiom and SKIPS the proof check.
        // SOUNDNESS: see `clean_kernel::set_mm_axiom_only` — sound only because
        // pass-2 re-verifies every in-range proof and only pass-2 results ship.
        clean_kernel::set_mm_axiom_only(in_pass1);
        let phase_t0 = std::time::Instant::now();
        // Per-phase counters (each phase re-traverses the same prefix).
        let mut attempted = 0usize;
        let mut provable_ord = 0usize;

        for (stmt_idx, stmt) in resolved.statements.iter().enumerate() {
            // Drop every type whose last citation was an earlier statement — its kernel
            // constant and importer caches are now unreachable (memory bound).
            //
            // TWO-PASS: PASS 1 must NOT forget anything — the whole axiom environment
            // has to survive for pass-2. In `Single` and `Pass2` the original
            // `forget_at` (last-use over the WHOLE prefix) is sound: `Pass2`'s range
            // theorems may reference any earlier dep, and a dep is dropped only after
            // its last citation by ANY provable — so an in-range reuse is never
            // starved. (A tighter range-scoped drop is possible but the whole-prefix
            // last-use bound is already correct and matches the sequential verifier,
            // which is what count-equivalence requires.)
            // #4: a forked worker shares the PASS-1 env copy-on-write, so its inherited
            // types cost no extra RAM until touched — skip the last-use forget (its O(N)
            // forget_decl COW-churn is the main thing capping the parallel speedup). The
            // sequential path (`child_sink == None`) still forgets to bound memory.
            if !in_pass1 && child_sink.is_none() {
                if let Some(dead) = stmt_idx.checked_sub(1).and_then(|p| forget_at.get(&p)) {
                    for label in dead {
                        let kn = kernel_name(label);
                        env.forget_decl(&clean_kernel::Name::from_string(&kn));
                        cache.remove(label);
                        sigs.remove(&kn);
                        guards.remove(&kn);
                        guard_counts.remove(&kn);
                        dummy_frames.remove(&kn);
                    }
                }
            }
            let ResolvedStatement::Assertion(a) = stmt else {
                continue;
            };
            if a.kind != "provable" {
                continue;
            }
            if attempted >= max_provables {
                break;
            }
            attempted += 1;
            // Provable ordinal of THIS theorem (0-based among `$p` statements).
            let this_ord = provable_ord;
            provable_ord += 1;
            // PASS 2: a theorem whose ordinal is OUTSIDE this worker's range keeps its
            // pass-1 axiom (its TYPE) so in-range dependents resolve, but its PROOF is
            // not re-checked here — it is verified by whichever worker owns its range.
            // We register it as an axiom (flag ON) so the bookkeeping below
            // (`sigs`/`cache`/…) runs identically to pass-1, then skip the `verified`
            // push. Range theorems get the flag OFF (real proof check).
            // #4: a forked worker only proof-checks ordinals where `ord % n == idx`
            // (strided → even cost split); the rest are out-of-range for it and skipped
            // below (their TYPE is already the inherited PASS-1 axiom).
            let in_range = pass2_range.as_ref().is_none_or(|r| r.contains(&this_ord))
                && stride.is_none_or(|(idx, n)| this_ord % n == idx);
            if pass2_range.is_some() {
                clean_kernel::set_mm_axiom_only(!in_range);
            }
            // Only a REAL proof verification (Single mode, or an in-range pass-2
            // theorem) contributes to `report` (verified/failed/skipped). PASS 1 and
            // out-of-range pass-2 theorems only build the dependency-type axiom
            // environment; their outcomes are not the verification result.
            let real_verification = !in_pass1 && in_range;

            // #4 fork worker: out-of-range PASS-2 theorems already have their TYPE (a PASS-1
            // axiom) in the COW-inherited env, so skip rebuilding/re-axiom-ing them. This is
            // what makes the parallel verify actually parallel — each worker only does its
            // own slice instead of re-axiom-ing the whole prefix. (The non-forked path keeps
            // re-axiom-ing, so sequential behavior is unchanged.) Validated byte-identical.
            if child_sink.is_some() && !in_pass1 && !in_range {
                continue;
            }

            // RANGE-SCOPED PASS-1: in PASS 1, register a `$p` theorem's TYPE only if
            // its label is in `reuse_set` (the deps the worker's `[a,b)` range reuses,
            // transitively closed). Skip the rest — they would only bloat pass-1's
            // resident set. The ordinal/attempt counters are already advanced above, so
            // pass-2's ordinals stay aligned; we just don't `build_tree` or register
            // this theorem. SOUND: a wrongly-skipped needed type makes a pass-2 reuse
            // fail-closed (the theorem is skipped), never a false accept — see the
            // `reuse_set` comment. Pass-2 (`!in_pass1`) and `Single`/`Pass1` (reuse_set
            // is `None`) are unaffected.
            if in_pass1 {
                if let Some(keep) = &reuse_set {
                    if !keep.contains(&a.label) {
                        continue;
                    }
                }
            }

            let hyp_index = hyp_index_of(a);
            let (proved, tree) = match build_tree(a, &resolved, &mut interner, &hyp_index, &cache) {
                Ok(pair) => pair,
                Err(MetamathError::InvalidStatement(reason))
                    if reason.starts_with("unsupported") =>
                {
                    if real_verification {
                        report.skipped.push((a.label.clone(), reason));
                    }
                    continue;
                }
                Err(e) => {
                    if real_verification {
                        report.failed.push((a.label.clone(), e.to_string()));
                    }
                    continue;
                }
            };

            // M13-dummy: α-rename this proof's DIRECT dummy work variables to globally-
            // fresh codes `∉ vu`, registering a fresh `$f` float-axiom for each. A fresh
            // dummy is then a fixed constant (applySubstV ignores it) whose `$d`
            // obligations discharge trivially, and — being distinct from every real
            // variable — can never collide with a reuser's substitution (the `sbt`/`sbtru`
            // self-pair `disjPair(y,y)` bug). Transitive dummies of REUSED theorems are
            // already fresh (renamed when those theorems were processed).
            let tree = {
                let mut direct: std::collections::BTreeMap<u64, (u64, String)> =
                    std::collections::BTreeMap::new();
                collect_direct_dummies(&tree, &float_axiom_names, &axiom_map, &mut direct);
                if direct.is_empty() {
                    tree
                } else {
                    let mut code_map: HashMap<u64, u64> = HashMap::new();
                    let mut float_rename: HashMap<String, String> = HashMap::new();
                    for (d, (tc, float_name)) in &direct {
                        let fresh = fresh_dummy_ctr;
                        fresh_dummy_ctr += 1;
                        let fresh_float = format!("mm.~dfloat~{fresh}");
                        clean_kernel::metamath_reflect::register_float_axiom(
                            &mut env,
                            &fresh_float,
                            *tc,
                            fresh,
                        )
                        .map_err(|e| {
                            MetamathError::InvalidStatement(format!(
                                "register fresh dummy float: {e}"
                            ))
                        })?;
                        float_axiom_names.insert(fresh_float.clone());
                        axiom_map.insert(fresh_float.clone(), (Vec::new(), vec![*tc, fresh]));
                        sigs.insert(fresh_float.clone(), (Vec::new(), vec![*tc, fresh]));
                        code_map.insert(*d, fresh);
                        float_rename.insert(float_name.clone(), fresh_float);
                    }
                    rename_tree_dummies(&tree, &code_map, &float_rename)
                }
            };

            let (float_hyps, essential_hyps, conclusion) = frame_of(a, &mut interner);
            // M13 ROUTING. `$d`-FREE & DUMMY-FREE → fast pure-schematic path. A proof that
            // applies a guarded assertion (a `$d`-axiom or a verified `$d`/dummy theorem)
            // OR floats a DUMMY/work variable takes the SCHEMATIC-`$d` path: the kernel
            // discharges each step's `$d` from the theorem's guard hypotheses (general
            // compound keystone discharge) AND each dummy float-leaf / reused dummy
            // theorem's σ-fixes-d obligation from the theorem's TRANSITIVE fix-d guards —
            // registering `Π σ, [fix-d …] → [$d …] → MMThm hyps → C`, SCHEMATICALLY
            // REUSABLE. If a guard can't be discharged it returns Err → GROUND guarded
            // fallback (sound; a dummy theorem can't be reused there, it just skips). A
            // guarded/dummy proof that verifies neither way is SKIPPED (fail-closed),
            // never falsely accepted.
            let uses_guarded = tree_uses_guarded(&tree, &guards);
            let kn = kernel_name(&a.label);
            let thm_disjoints: Vec<(u64, u64)> = a
                .disjoints
                .iter()
                .map(|(x, y)| (interner.intern(x), interner.intern(y)))
                .collect();
            // Transitive dummy frame: the work variables this proof floats directly plus
            // those of every dummy theorem it reuses.
            let dummies: Vec<u64> = {
                let mut s = std::collections::BTreeSet::new();
                collect_dummy_frame(&tree, &float_axiom_names, &axiom_map, &dummy_frames, &mut s);
                s.into_iter().collect()
            };
            // Freshness `$d` obligations of each dummy: distinct from every mandatory
            // variable and every other dummy (OVER-APPROXIMATE — extra `disjPair` guards
            // only WEAKEN the `Π σ` claim, so at worst a reuse can't discharge one and
            // skips; never a false accept). Merged with the theorem's own `$d` frame.
            let full_disjoints: Vec<(u64, u64)> = {
                let mandatory: Vec<u64> = float_hyps.iter().map(|&(_, v)| v).collect();
                let mut seen: hashbrown::HashSet<(u64, u64)> =
                    thm_disjoints.iter().copied().collect();
                let mut out = thm_disjoints.clone();
                for &d in &dummies {
                    for &v in mandatory.iter().chain(dummies.iter()) {
                        if v != d && seen.insert((d, v)) {
                            out.push((d, v));
                        }
                    }
                }
                out
            };
            let needs_schematic_dv = uses_guarded || !dummies.is_empty();
            let run = |env: &mut Environment,
                       sigs: &hashbrown::HashMap<String, (Vec<Vec<u64>>, Vec<u64>)>,
                       guards: &hashbrown::HashMap<String, Vec<(u64, u64)>>,
                       guard_counts: &std::collections::HashMap<String, usize>,
                       dummy_frames: &hashbrown::HashMap<String, Vec<u64>>|
             -> (Result<(), clean_kernel::KernelEnvError>, bool) {
                // TWO-PASS LIGHT PASS-1 (axiom-only mode ON: pass-1, or an out-of-range
                // pass-2 theorem). Register ONLY the schematic-`$d` TYPE, SKIPPING the
                // expensive embedding derivation (`build_schematic_derivation`) that the
                // full path builds and `add_decl` then immediately throws away under
                // `set_mm_axiom_only`. The type is built from the FRAME alone (frame +
                // `$d` frame `full_disjoints` + dummy frame `dummies` + var universe), so
                // it is byte-identical to the type the full SUCCESS path registers — and
                // this is the dominant pass-1 cost (deep proofs `impsingle-*`/`moi2`/
                // `cbvralf`: tens of seconds each, ALL wasted).
                //
                // The light path always registers the SCHEMATIC type and marks the
                // theorem reusable — matching the full SUCCESS path. A `needs_schematic_dv`
                // theorem whose full path would instead FALL BACK to the GROUND (non-
                // reusable) shape is the only divergence; it is SOUND because pass-2
                // RE-VERIFIES every in-range proof, and a wrong (schematic-vs-ground) type
                // only ever makes a reusing proof FAIL-CLOSED (skip), never a false accept
                // — exactly the sequential verifier's own behaviour for a ground theorem,
                // so count-equivalence is preserved. Validated by the two-pass+gate ==
                // sequential count check. See `register_metamath_theorem_type_light`.
                if clean_kernel::mm_axiom_only() {
                    let (disj, fixd): (&[(u64, u64)], &[u64]) = if needs_schematic_dv {
                        (&full_disjoints, &dummies)
                    } else {
                        (&[], &[])
                    };
                    let r = clean_kernel::metamath_reflect::register_metamath_theorem_type_light(
                        env,
                        &kn,
                        &float_hyps,
                        &essential_hyps,
                        &conclusion,
                        disj,
                        &var_universe,
                        fixd,
                    );
                    return (r, true);
                }
                if needs_schematic_dv {
                    let r = verify_metamath_theorem_schematic_dv(
                        env,
                        &kn,
                        &float_hyps,
                        &essential_hyps,
                        &conclusion,
                        &tree,
                        sigs,
                        &full_disjoints,
                        &var_universe,
                        guards,
                        &dummies,
                        &float_axiom_names,
                        dummy_frames,
                    );
                    if r.is_ok() {
                        (r, true)
                    } else {
                        let g = verify_metamath_theorem_guarded(
                            env,
                            &kn,
                            &float_hyps,
                            &essential_hyps,
                            &conclusion,
                            &tree,
                            guard_counts,
                        );
                        (g, false)
                    }
                } else {
                    let r = verify_metamath_theorem_schematic(
                        env,
                        &kn,
                        &float_hyps,
                        &essential_hyps,
                        &conclusion,
                        &tree,
                        sigs,
                        &var_universe,
                    );
                    (r, true)
                }
            };
            // Opt-in per-theorem timing (`CLEAN_MM_PROF=1`): emits `PROF SLOW <label>
            // first=<s>` for any theorem whose FIRST kernel-verification attempt exceeds
            // 0.5 s, and `PROF RETRY <label> first=<s> retry=<s>` when the cache-off
            // retry below actually fires. This is the diagnostic that established the
            // deep-proof speed wall is the first-attempt `is_def_eq` exploration on
            // pathologically deep proofs (single-axiom logic `impsingle-*`, deep
            // substitution `sbco4OLD`/`sb*` — 0.5–55 s each), NOT the retry (which fires
            // on ~2/3300). See docs + the kernel-perf TODO. Overhead when unset: two
            // `Instant::now()` calls per theorem (negligible).
            let prof = std::env::var("CLEAN_MM_PROF").is_ok();
            if prof {
                clean_kernel::reduction_stats_reset();
            }
            // PASS 2: drop this theorem's PASS-1 axiom so `run`'s `add_decl` can
            // re-register `mm.<label>` (otherwise it hits `DuplicateName`). For an
            // IN-RANGE theorem the flag is OFF, so `run` re-adds it as a checked
            // `Theorem` (the real proof verification). For an OUT-OF-RANGE theorem the
            // flag is ON, so `run` re-registers the same TYPE as an axiom (no proof
            // check) — keeping the bookkeeping below identical to pass-1.
            if pass2_range.is_some() {
                env.forget_decl(&clean_kernel::Name::from_string(&kn));
            }
            let t_first = std::time::Instant::now();
            let (mut outcome, mut reusable) =
                run(&mut env, &sigs, &guards, &guard_counts, &dummy_frames);
            let first_secs = t_first.elapsed().as_secs_f64();
            // A long proof can still trip the cache-size def-eq false-negative; retry
            // once with the TC cache bounded to 0 (sound — only converts a spurious
            // rejection into a correct acceptance). BUT skip this retry for a
            // HeartbeatExceeded timeout (CLEAN_MM_HEARTBEAT cap hit): a cold cache only
            // makes the proof SLOWER and it would time out again, so retrying just
            // doubles the per-skip cost. The retry only ever fixes a cache-size def-eq
            // false-NEGATIVE — a heartbeat timeout is not that. Halves the cost of
            // skipping pathological proofs, keeping full coverage at the chosen cap.
            let hb_exceeded = outcome
                .as_ref()
                .err()
                .map(|e| e.to_string().contains("heartbeat limit exceeded"))
                .unwrap_or(false);
            if outcome.is_err() && !hb_exceeded && std::env::var("CLEAN_MM_CACHE").is_err() {
                let t_retry = std::time::Instant::now();
                env.set_option("tcMaxCacheEntries".to_string(), Some("0".to_string()));
                let (o, r) = run(&mut env, &sigs, &guards, &guard_counts, &dummy_frames);
                outcome = o;
                reusable = r;
                env.set_option("tcMaxCacheEntries".to_string(), None);
                if prof {
                    use std::io::Write;
                    let _ = writeln!(
                        std::io::stderr(),
                        "PROF RETRY {} first={first_secs:.2}s retry={:.2}s",
                        a.label,
                        t_retry.elapsed().as_secs_f64()
                    );
                    let _ = std::io::stderr().flush();
                }
            } else if prof && first_secs > 0.5 {
                use std::io::Write;
                let _ = writeln!(
                    std::io::stderr(),
                    "PROF SLOW {} first={first_secs:.2}s\n{}",
                    a.label,
                    clean_kernel::reduction_stats_report(6)
                );
                let _ = std::io::stderr().flush();
            }
            match outcome {
                Ok(()) => {
                    if real_verification {
                        report.verified.push(a.label.clone());
                    }
                    // Flushed progress (opt-in) so a long run that is interrupted still
                    // yields a confirmed lower-bound count. `failed` is printed too: any
                    // nonzero value is a soundness alarm.
                    if std::env::var("CLEAN_MM_PROGRESS").is_ok()
                        && report.verified.len() % 2000 == 0
                    {
                        use std::io::Write;
                        let _ = writeln!(
                            std::io::stderr(),
                            "PROGRESS verified={} failed={} attempted={}",
                            report.verified.len(),
                            report.failed.len(),
                            attempted
                        );
                        let _ = std::io::stderr().flush();
                    }
                    // Schematic (incl. schematic-$d / dummy) theorems are reusable.
                    if reusable {
                        // BOTH-ORDERS `$d` + freshness guard frame so dependents discharge
                        // its `disjPair` guards. `guard_counts` (GROUND-path reuse) is set
                        // only when there are NO fix-d guards: a dummy theorem's σ-fixes-d
                        // arrows are List-`Eq`, not Bool `Eq.refl`, so a ground reuse must
                        // fail-closed (no count ⇒ arity mismatch ⇒ skip), never accept.
                        //
                        // GATE on `needs_schematic_dv`: a theorem only carries guard arrows
                        // in its registered type if it went through the schematic-`$d` path.
                        // A theorem that merely DECLARES `$d` but proves its goal from purely
                        // `$d`-free assertions (e.g. `ax6v`/`ax6ev` — `ax-6` + `df-ex`) takes
                        // the PLAIN schematic path (`Π σ, MMThm C`, all-σ, SOUND because the
                        // proof itself is `$d`-free) and has NO guard arrows. Logging it in
                        // `guards` made dependents discharge phantom guards, shoving a guard
                        // proof where the theorem expects its first `$f` float hyp →
                        // `EXP=[setvar x] INF=[]` rejection. Such pure theorems must NOT be
                        // guarded for reuse.
                        if needs_schematic_dv && !full_disjoints.is_empty() {
                            let bo = both_orders(&full_disjoints);
                            if dummies.is_empty() {
                                guard_counts.insert(kn.clone(), bo.len());
                            }
                            guards.insert(kn.clone(), bo);
                        }
                        // Transitive dummy frame so dependents carry + discharge the
                        // σ-fixes-d guards this theorem's `Π σ` requires.
                        if !dummies.is_empty() {
                            dummy_frames.insert(kn.clone(), dummies.clone());
                        }
                        let mut hf: Vec<Vec<u64>> =
                            float_hyps.iter().map(|&(tc, v)| vec![tc, v]).collect();
                        hf.extend(essential_hyps.iter().cloned());
                        sigs.insert(kn.clone(), (hf, conclusion.clone()));
                        cache.insert(a.label.clone(), CachedTheorem { tree });
                    }
                    // Disposition of the just-verified `(type, value)` (both the
                    // schematic and guarded ground path register `mm.<label>` with its
                    // value). `Collect` accumulates the clones into `verified_exprs`;
                    // `Stream` hands them to a sink (the streaming shard export) and then
                    // drops the value; `CountOnly` just drops it. Dropping the proof
                    // VALUE (forget_value) is what keeps peak memory bounded — without it
                    // the Environment retains ~3 MB/theorem and the full ~25-30k run
                    // OOM-thrashes a 24 GB host. Soundness + count-equivalence: see
                    // Environment::forget_value.
                    let kn_name = clean_kernel::Name::from_string(&kn);
                    match &mut mode {
                        CollectMode::Collect => {
                            if let Some(ci) = env.get_const(&kn_name) {
                                if let Some(val) = ci.value.clone() {
                                    report
                                        .verified_exprs
                                        .push((kn.clone(), ci.type_.clone(), val));
                                }
                            }
                        }
                        CollectMode::Stream(sink) => {
                            // Clone (type, value) out, releasing the immutable borrow,
                            // then forget the value so it never accumulates in the env.
                            let pair = env
                                .get_const(&kn_name)
                                .and_then(|ci| ci.value.clone().map(|v| (ci.type_.clone(), v)));
                            if let Some((ty, val)) = pair {
                                sink(&kn, &ty, &val);
                            }
                            env.forget_value(&kn_name);
                        }
                        CollectMode::CountOnly => {
                            env.forget_value(&kn_name);
                        }
                        CollectMode::Pass1Types { wanted, sink } => {
                            // Axiom-only pass: `mm.<label>` is registered as an axiom
                            // (no value). Emit its kernel-registered TYPE for export,
                            // but ONLY for labels the caller asked for — a dependency
                            // registered solely to build a wanted type is never emitted.
                            if wanted.contains(&a.label) {
                                if let Some(ci) = env.get_const(&kn_name) {
                                    sink(&a.label, &kn, &ci.type_.clone());
                                }
                            }
                        }
                    }
                }
                Err(e) => {
                    // PASS 1 / OUT-OF-RANGE pass-2: this `run` only registered a TYPE
                    // as an axiom (no proof check). An Err here means the type itself
                    // was rejected (malformed schematic build) — record nothing and
                    // move on; the theorem will be (re-)attempted as a real proof by
                    // whichever worker owns its range. Never pollute failed/skipped
                    // with a non-verification.
                    if !real_verification {
                        let _ = &e;
                        continue;
                    }
                    // A guarded ($d) or dummy theorem that neither the schematic-$d nor
                    // the ground path could verify is SKIPPED (fail-closed), not failed:
                    // a missing cross-pair guard (the general compound discharge) or a
                    // dummy-variable obstruction — a coverage gap, not a soundness
                    // violation or a bad proof.
                    if needs_schematic_dv {
                        report.skipped.push((
                            a.label.clone(),
                            "unsupported: $d obligation undischargeable (missing guard / dummy)"
                                .to_string(),
                        ));
                        continue;
                    }
                    // Diagnostic: does the RPN-tracked conclusion match the claim?
                    let tag = if proved == a.formula {
                        "tracked==claim"
                    } else {
                        "tracked!=claim"
                    };
                    // Faithful Rust re-check of the tree (forms + arity + hyps): if
                    // this ACCEPTS but the kernel rejects, the tree is a valid
                    // Metamath proof and the issue is a kernel-interaction one on
                    // large inlined terms — not a translation bug.
                    let mut hyp_forms: Vec<Vec<u64>> =
                        float_hyps.iter().map(|&(tc, v)| vec![tc, v]).collect();
                    hyp_forms.extend(essential_hyps.iter().cloned());
                    let rev = interner.reverse();
                    let detail = match recheck(&tree, &axiom_map, &hyp_forms) {
                        Ok(_) => "recheck OK".to_string(),
                        Err(m) => m.decode(&rev),
                    };
                    let kdecode = decode_kernel_mismatch(&env, &e, &rev).unwrap_or_else(|| {
                        let s = e.to_string();
                        s.chars().take(180).collect::<String>()
                    });
                    report.failed.push((
                        a.label.clone(),
                        format!(
                            "[{tag}] tree_size={} {detail} | kernel: {kdecode}",
                            tree_size(&tree)
                        ),
                    ));
                }
            }
        } // end inner per-statement loop
        if std::env::var("CLEAN_MM_PROF").is_ok() {
            use std::io::Write;
            let pname = if in_pass1 {
                "PASS1-register-types"
            } else if pass2_range.is_some() {
                "PASS2-verify-range"
            } else {
                "SINGLE"
            };
            let _ = writeln!(
                std::io::stderr(),
                "PROF PHASE {pname} attempted={attempted} elapsed={:.2}s env_constants={}",
                phase_t0.elapsed().as_secs_f64(),
                env.num_constants()
            );
            let _ = std::io::stderr().flush();
        }
        // #4: a forked PASS-2 worker writes its verified ("V ") AND failed ("F ") labels
        // to its sink and exits; the parent unions them in fork_parallel_pass2. Failures
        // are propagated so a soundness alarm in any worker still surfaces to the driver.
        if let Some(sink) = &child_sink {
            let mut buf = String::with_capacity(report.verified.len() * 8);
            for l in &report.verified {
                buf.push_str("V ");
                buf.push_str(l);
                buf.push('\n');
            }
            for (l, _) in &report.failed {
                buf.push_str("F ");
                buf.push_str(l);
                buf.push('\n');
            }
            let _ = std::fs::write(sink, buf);
            use std::io::Write;
            let _ = std::io::stderr().flush();
            std::process::exit(0);
        }
        // Clear axiom-only mode at the end of each phase so a subsequent phase
        // (pass-2) — and any later code on this thread — runs the checked path.
        clean_kernel::set_mm_axiom_only(false);
    } // end outer per-phase loop

    Ok(report)
}

/// Resolve the `MM_PARALLEL` worker count for fork-COW parallel PASS-2.
/// A positive integer is used as-is; `auto` picks (physical cores − 1), clamped to a
/// value that keeps copy-on-write growth from swapping a small machine on large N
/// (override with an explicit number for more/fewer); unset/unparseable → sequential.
#[cfg(unix)]
fn mm_parallel_workers() -> usize {
    match std::env::var("MM_PARALLEL").ok().as_deref() {
        Some("auto") | Some("AUTO") => std::thread::available_parallelism()
            .map(|n| n.get().saturating_sub(1))
            .unwrap_or(1)
            .clamp(1, 12),
        Some(s) => s.parse::<usize>().ok().filter(|&n| n >= 1).unwrap_or(1),
        None => 1,
    }
}

/// Role returned by [`fork_parallel_pass2`] (#4 shared-env parallelism).
#[cfg(unix)]
enum ParallelRole {
    /// This process is forked PASS-2 worker `idx` of `n`: verify the ordinals in `full`
    /// where `ord % n == idx` (STRIDED so each worker gets an even mix of cheap + expensive
    /// theorems), then write labels to `sink` + exit.
    Child {
        idx: usize,
        n: usize,
        full: std::ops::Range<usize>,
        sink: std::path::PathBuf,
    },
    /// This process is the parent; the children's labels are already in `report`.
    ParentDone,
}

/// Fork `workers` PASS-2 children over disjoint contiguous sub-ranges of `full`, sharing the
/// already-built PASS-1 env copy-on-write (1×env, not N×env). Each child returns
/// [`ParallelRole::Child`] to verify its sub-range then write+exit; the parent `waitpid`s every
/// child, unions their `V `/`F ` labels into `report`, and returns [`ParallelRole::ParentDone`].
///
/// SOUNDNESS: every child verifies its sub-range against the IDENTICAL post-PASS-1 env the
/// sequential verifier uses (PASS-2 is the same checked path), so the unioned verified set is
/// byte-identical to sequential. A worker that fails to fork or dies just contributes no labels
/// (fail-closed) — never a false accept; a worker that hits a real FAIL writes it ("F ") so the
/// parent still surfaces the soundness alarm.
#[cfg(unix)]
fn fork_parallel_pass2(
    full: &std::ops::Range<usize>,
    workers: usize,
    report: &mut KernelVerifyReport,
) -> ParallelRole {
    let dir = std::env::temp_dir().join(format!("mm_par_{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let mut kids: Vec<(libc::pid_t, std::path::PathBuf)> = Vec::new();
    for i in 0..workers {
        let sink = dir.join(format!("w{i}.txt"));
        // Flush inherited stdio so children never replay buffered bytes.
        use std::io::Write;
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
        // SAFETY: single-threaded here (PASS-1 + setup are sequential; no rayon pool runs on
        // this path), so fork() leaves no lock held by a vanished thread. The child only
        // reads / COW-mutates inherited memory and writes its own result file before exit.
        let pid = unsafe { libc::fork() };
        if pid == 0 {
            return ParallelRole::Child {
                idx: i,
                n: workers,
                full: full.clone(),
                sink,
            };
        } else if pid > 0 {
            kids.push((pid, sink));
        } else {
            eprintln!(
                "warn: fork failed for PASS-2 worker {i}/{workers}; its labels will be missing \
                 (lower MM_PARALLEL)"
            );
        }
    }
    for (pid, sink) in &kids {
        let mut status: libc::c_int = 0;
        unsafe {
            libc::waitpid(*pid, &mut status, 0);
        }
        if let Ok(s) = std::fs::read_to_string(sink) {
            for line in s.lines() {
                if let Some(l) = line.strip_prefix("V ") {
                    report.verified.push(l.to_string());
                } else if let Some(l) = line.strip_prefix("F ") {
                    report
                        .failed
                        .push((l.to_string(), "forked PASS-2 worker".to_string()));
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    ParallelRole::ParentDone
}

/// Map a theorem's hypotheses (mandatory floats then essentials) to indices.
fn hyp_index_of(a: &ResolvedAssertion) -> HashMap<String, usize> {
    let mut idx = HashMap::new();
    for (i, h) in a.mandatory_floats.iter().enumerate() {
        idx.insert(h.label.clone(), i);
    }
    let off = a.mandatory_floats.len();
    for (i, h) in a.essential_hyps.iter().enumerate() {
        idx.insert(h.label.clone(), off + i);
    }
    idx
}

/// Intern a theorem's frame: `(float_hyps, essential_hyps, conclusion)`.
fn frame_of(
    a: &ResolvedAssertion,
    interner: &mut Interner,
) -> (Vec<(u64, u64)>, Vec<Vec<u64>>, Vec<u64>) {
    let float_hyps = a
        .mandatory_floats
        .iter()
        .map(|h| (interner.intern(&h.typecode), interner.intern(&h.variable)))
        .collect();
    let essential_hyps = a
        .essential_hyps
        .iter()
        .map(|h| interner.form(&h.formula))
        .collect();
    let conclusion = interner.form(&a.formula);
    (float_hyps, essential_hyps, conclusion)
}

/// One decoded proof instruction.
enum Step {
    /// Apply a labelled statement.
    Label(String),
    /// Mark the most recent step's result for later back-reference (`Z`).
    Save,
    /// Push a previously-saved result (compressed back-reference).
    SavedRef(usize),
}

/// Decode a proof (uncompressed or compressed) into a flat instruction stream.
fn proof_steps(theorem: &ResolvedAssertion, proof: &Proof) -> MetamathResult<Vec<Step>> {
    match proof {
        Proof::Uncompressed(labels) => Ok(labels.iter().cloned().map(Step::Label).collect()),
        Proof::Compressed(c) => decode_compressed(theorem, c),
    }
}

/// Decode a compressed proof (Metamath book §4.4): the number alphabet
/// `A-T` (low, base-20) / `U-Y` (high, base-5, +1) yields an index into
/// `mandatory hyps ++ parenthesised labels ++ saved steps`; `Z` saves a step.
fn decode_compressed(
    theorem: &ResolvedAssertion,
    c: &CompressedProof,
) -> MetamathResult<Vec<Step>> {
    let mut label_table: Vec<String> = theorem
        .mandatory_floats
        .iter()
        .map(|h| h.label.clone())
        .collect();
    label_table.extend(theorem.essential_hyps.iter().map(|h| h.label.clone()));
    label_table.extend(c.labels.iter().cloned());
    let label_count = label_table.len();

    let mut steps = Vec::new();
    let mut value = 0usize;
    let mut in_number = false;
    for ch in c.code.chars().filter(|ch| !ch.is_whitespace()) {
        match ch {
            'A'..='T' => {
                value = value
                    .checked_mul(20)
                    .and_then(|v| v.checked_add(ch as usize - 'A' as usize + 1))
                    .ok_or_else(|| {
                        MetamathError::InvalidStatement(format!(
                            "unsupported: compressed proof index overflow in {}",
                            theorem.label
                        ))
                    })?;
                in_number = false;
                if value <= label_count {
                    steps.push(Step::Label(label_table[value - 1].clone()));
                } else {
                    steps.push(Step::SavedRef(value - label_count - 1));
                }
                value = 0;
            }
            'U'..='Y' => {
                value = value
                    .checked_mul(5)
                    .and_then(|v| v.checked_add(ch as usize - 'U' as usize + 1))
                    .ok_or_else(|| {
                        MetamathError::InvalidStatement(format!(
                            "unsupported: compressed proof index overflow in {}",
                            theorem.label
                        ))
                    })?;
                in_number = true;
            }
            'Z' => {
                if in_number {
                    return Err(MetamathError::InvalidStatement(format!(
                        "unsupported: malformed compressed proof in {}",
                        theorem.label
                    )));
                }
                steps.push(Step::Save);
            }
            '?' => {
                return Err(MetamathError::InvalidStatement(format!(
                    "unsupported: incomplete proof (?) in {}",
                    theorem.label
                )))
            }
            other => {
                return Err(MetamathError::InvalidStatement(format!(
                    "unsupported: bad compressed char {other:?} in {}",
                    theorem.label
                )))
            }
        }
    }
    if in_number {
        return Err(MetamathError::InvalidStatement(format!(
            "unsupported: unterminated compressed code in {}",
            theorem.label
        )));
    }
    Ok(steps)
}

/// Replay a proof's RPN stack machine, emitting an [`MMProofTree`] (tracking
/// each stack entry's [`Formula`] so substitutions can be read off the
/// floating-hypothesis arguments). Steps that apply an earlier `$p` theorem are
/// resolved by INLINING that theorem's cached axiom-expanded tree under the
/// call-site substitution. Handles compressed proofs' `Z`-save / back-reference.
fn build_tree(
    theorem: &ResolvedAssertion,
    resolved: &ResolvedDatabase,
    interner: &mut Interner,
    hyp_index: &HashMap<String, usize>,
    cache: &HashMap<String, CachedTheorem>,
) -> MetamathResult<(Formula, MMProofTree)> {
    let proof = theorem.proof.as_ref().ok_or_else(|| {
        MetamathError::InvalidStatement(format!("missing proof for {}", theorem.label))
    })?;
    let steps = proof_steps(theorem, proof)?;

    let mut stack: Vec<(Formula, MMProofTree)> = Vec::new();
    let mut saved: Vec<(Formula, MMProofTree)> = Vec::new();
    let mut last: Option<(Formula, MMProofTree)> = None;

    for step in steps {
        match step {
            Step::Label(label) => {
                let entry = apply_label(
                    &label, theorem, resolved, interner, hyp_index, cache, &mut stack,
                )?;
                last = Some(entry);
            }
            Step::Save => {
                let entry = last.clone().ok_or_else(|| {
                    MetamathError::InvalidStatement(format!(
                        "unsupported: Z before any step in {}",
                        theorem.label
                    ))
                })?;
                saved.push(entry);
            }
            Step::SavedRef(i) => {
                let entry = saved.get(i).cloned().ok_or_else(|| {
                    MetamathError::InvalidStatement(format!(
                        "unsupported: compressed back-reference out of range in {}",
                        theorem.label
                    ))
                })?;
                stack.push(entry.clone());
                last = Some(entry);
            }
        }
    }

    if stack.len() != 1 {
        return Err(MetamathError::FinalResultMismatch {
            theorem: theorem.label.clone(),
        });
    }
    Ok(stack.pop().expect("stack length checked"))
}

/// Apply one labelled proof step: push the corresponding stack entry and return
/// it (a floating/essential hypothesis, or an assertion application — with `$p`
/// reuse inlined). The pushed entry is also returned for `Z`-save tracking.
#[allow(clippy::too_many_arguments)]
fn apply_label(
    label: &str,
    theorem: &ResolvedAssertion,
    resolved: &ResolvedDatabase,
    interner: &mut Interner,
    hyp_index: &HashMap<String, usize>,
    cache: &HashMap<String, CachedTheorem>,
    stack: &mut Vec<(Formula, MMProofTree)>,
) -> MetamathResult<(Formula, MMProofTree)> {
    let stmt = resolved
        .get(label)
        .ok_or_else(|| MetamathError::UnknownLabel {
            theorem: theorem.label.clone(),
            label: label.to_string(),
        })?;
    let entry = match stmt {
        ResolvedStatement::Floating(h) => {
            let formula = Formula {
                typecode: h.typecode.clone(),
                tokens: vec![h.variable.clone()],
            };
            match hyp_index.get(label).copied() {
                // Mandatory float → the theorem's own hypothesis.
                Some(idx) => (formula, MMProofTree::Hyp(idx)),
                // Non-mandatory (DUMMY/work) variable → its typing comes from the
                // `$f` float-axiom `mm.<flabel> : MMThm([tc,var])`, applied at the
                // identity substitution. Routes the theorem to the ground path.
                None => (
                    formula,
                    MMProofTree::Apply {
                        assertion: kernel_name(label),
                        subst: vec![],
                        args: vec![],
                    },
                ),
            }
        }
        ResolvedStatement::Essential(h) => {
            let idx = hyp_index.get(label).copied().ok_or_else(|| {
                MetamathError::InvalidStatement(format!(
                    "unsupported: proof of {} uses non-mandatory essential hyp {label}",
                    theorem.label
                ))
            })?;
            (h.formula.clone(), MMProofTree::Hyp(idx))
        }
        ResolvedStatement::Assertion(a) => {
            let n = a.mandatory_floats.len() + a.essential_hyps.len();
            if stack.len() < n {
                return Err(MetamathError::StackUnderflow {
                    theorem: theorem.label.clone(),
                    label: label.to_string(),
                });
            }
            let args: Vec<(Formula, MMProofTree)> = stack.split_off(stack.len() - n);

            // Substitution from the floating-hypothesis arguments (the first
            // `mandatory_floats.len()` popped entries): string form (to track
            // the resulting stack formula) and interned form (to build the
            // kernel `subst` / inline `$p` reuse).
            let mut subst_str: HashMap<String, Vec<String>> = HashMap::new();
            let mut subst_pairs: Vec<(u64, Vec<u64>)> = Vec::new();
            let mut subst_codes: HashMap<u64, Vec<u64>> = HashMap::new();
            for (arg, hyp) in args.iter().zip(a.mandatory_floats.iter()) {
                subst_str.insert(hyp.variable.clone(), arg.0.tokens.clone());
                let var = interner.intern(&hyp.variable);
                let repl = interner.tokens(&arg.0.tokens);
                subst_codes.insert(var, repl.clone());
                subst_pairs.push((var, repl));
            }

            let result = instantiate(&a.formula, &subst_str);
            let arg_trees: Vec<MMProofTree> = args.into_iter().map(|(_, t)| t).collect();

            // Both `$a` axioms and verified `$p` theorems are registered kernel
            // constants (`mm.<label>`), applied here at the call-site
            // substitution — SCHEMATIC reuse, no inlining, so the term stays
            // small. A `$p` is reusable only once it has verified (is in `cache`).
            let _ = &subst_codes;
            // `$d`-constrained axioms (e.g. ax-5) ARE applied here: the registrar
            // gave them `disjPair … = true` GUARD arrows, and the GROUND guarded
            // verification path discharges those so the kernel enforces the
            // disjoint-variable condition. (The verify loop routes any proof that
            // applies one to that path.) A reused `$p` theorem must still have
            // verified ($d-free schematic theorems are in `cache`; $d-bearing ones
            // are ground-only, so reusing them stays skipped).
            if a.kind != "axiom" && !cache.contains_key(&a.label) {
                return Err(MetamathError::InvalidStatement(format!(
                    "unsupported: proof of {} reuses $p theorem {label} that did not verify",
                    theorem.label
                )));
            }
            let tree = MMProofTree::Apply {
                assertion: kernel_name(&a.label),
                subst: subst_pairs,
                args: arg_trees,
            };
            (result, tree)
        }
    };
    stack.push(entry.clone());
    Ok(entry)
}

/// Inline a cached `$p` theorem's tree at a call site: apply the call-site
/// substitution `sigma` (the theorem's variable codes → replacement forms) to
/// every form inside, and replace each `Hyp(j)` with the call-site argument
/// `use_args[j]`. The result references only `$a` axioms and the OUTER theorem's
/// hypotheses.
fn inline_tree(
    node: &MMProofTree,
    sigma: &HashMap<u64, Vec<u64>>,
    use_args: &[MMProofTree],
) -> MMProofTree {
    match node {
        MMProofTree::Hyp(j) => use_args[*j].clone(),
        MMProofTree::Apply {
            assertion,
            subst,
            args,
        } => MMProofTree::Apply {
            assertion: assertion.clone(),
            subst: subst
                .iter()
                .map(|(v, form)| (*v, apply_codes(sigma, form)))
                .collect(),
            args: args
                .iter()
                .map(|a| inline_tree(a, sigma, use_args))
                .collect(),
        },
    }
}

/// Apply an interned substitution to an interned form (symbol-list splice).
fn apply_codes(sigma: &HashMap<u64, Vec<u64>>, form: &[u64]) -> Vec<u64> {
    let mut out = Vec::with_capacity(form.len());
    for &s in form {
        if let Some(r) = sigma.get(&s) {
            out.extend_from_slice(r);
        } else {
            out.push(s);
        }
    }
    out
}

/// Apply a substitution to a form using FIRST-match semantics over the binding
/// list — mirroring the kernel's nested-`iteList` `subst_fn` exactly.
fn apply_first(subst: &[(u64, Vec<u64>)], form: &[u64]) -> Vec<u64> {
    let mut out = Vec::with_capacity(form.len());
    for &s in form {
        match subst.iter().find(|(v, _)| *v == s) {
            Some((_, r)) => out.extend_from_slice(r),
            None => out.push(s),
        }
    }
    out
}

/// Number of nodes in a proof tree.
fn tree_size(node: &MMProofTree) -> usize {
    match node {
        MMProofTree::Hyp(_) => 1,
        MMProofTree::Apply { args, .. } => 1 + args.iter().map(tree_size).sum::<usize>(),
    }
}

/// Whether the proof tree applies any `$d`-constrained (tainted) axiom — such a
/// proof must be verified on the GROUND guarded path, where the kernel can enforce
/// the disjoint-variable side-condition (M12).
fn tree_uses(node: &MMProofTree, tainted: &hashbrown::HashSet<String>) -> bool {
    match node {
        MMProofTree::Hyp(_) => false,
        MMProofTree::Apply {
            assertion, args, ..
        } => tainted.contains(assertion) || args.iter().any(|a| tree_uses(a, tainted)),
    }
}

/// Whether the proof tree applies any GUARDED assertion — a `$d`-bearing axiom OR a
/// verified `$d`-bearing schematic theorem (anything in `guards`). Such a proof must
/// take the schematic-`$d` path so the kernel discharges those guards (M13).
fn tree_uses_guarded(
    node: &MMProofTree,
    guards: &hashbrown::HashMap<String, Vec<(u64, u64)>>,
) -> bool {
    match node {
        MMProofTree::Hyp(_) => false,
        MMProofTree::Apply {
            assertion, args, ..
        } => guards.contains_key(assertion) || args.iter().any(|a| tree_uses_guarded(a, guards)),
    }
}

/// M13-dummy: collect a proof's TRANSITIVE dummy frame — the work variables it
/// floats directly (a `$f` float-AXIOM leaf, whose `[tc, d]` conclusion is in
/// `axiom_map`) PLUS every dummy of a verified theorem it reuses (`dummy_frames`).
fn collect_dummy_frame(
    node: &MMProofTree,
    float_names: &hashbrown::HashSet<String>,
    axiom_map: &HashMap<String, (Vec<Vec<u64>>, Vec<u64>)>,
    dummy_frames: &hashbrown::HashMap<String, Vec<u64>>,
    out: &mut std::collections::BTreeSet<u64>,
) {
    if let MMProofTree::Apply {
        assertion, args, ..
    } = node
    {
        if float_names.contains(assertion) {
            if let Some((_, concl)) = axiom_map.get(assertion) {
                if concl.len() == 2 {
                    out.insert(concl[1]);
                }
            }
        }
        if let Some(frame) = dummy_frames.get(assertion) {
            out.extend(frame.iter().copied());
        }
        for a in args {
            collect_dummy_frame(a, float_names, axiom_map, dummy_frames, out);
        }
    }
}

/// Collect the DIRECT dummy floats of a proof tree: each `Apply` of a `$f`
/// float-AXIOM (a setvar/wff/class work variable introduced mid-proof, since
/// MANDATORY floats are `Hyp` nodes) → `dummy_code -> (typecode, float_name)`.
fn collect_direct_dummies(
    node: &MMProofTree,
    float_names: &hashbrown::HashSet<String>,
    axiom_map: &HashMap<String, (Vec<Vec<u64>>, Vec<u64>)>,
    out: &mut std::collections::BTreeMap<u64, (u64, String)>,
) {
    if let MMProofTree::Apply {
        assertion, args, ..
    } = node
    {
        if float_names.contains(assertion) {
            if let Some((_, concl)) = axiom_map.get(assertion) {
                if concl.len() == 2 {
                    out.entry(concl[1]).or_insert((concl[0], assertion.clone()));
                }
            }
        }
        for a in args {
            collect_direct_dummies(a, float_names, axiom_map, out);
        }
    }
}

/// Rewrite a proof tree, renaming each dummy work variable to a globally-fresh
/// code OUTSIDE the variable universe: dummy float leaves get the fresh float
/// (`float_rename`), and dummy codes inside step substitutions are remapped
/// (`code_map`). A fresh code is `∉ vu`, so `applySubstV` FIXES it (treats it as a
/// constant) and its `$d` obligations discharge trivially (`varsOf` is empty) — this
/// makes the dummy globally distinct, so a reuser's substitution can never collide
/// with it (the `sbt`-dummy-`y` vs reuser-`y` self-pair bug). Sound: the fresh
/// constant is provably distinct from every real variable, exactly as Metamath's
/// implicit dummy α-renaming requires.
fn rename_tree_dummies(
    node: &MMProofTree,
    code_map: &HashMap<u64, u64>,
    float_rename: &HashMap<String, String>,
) -> MMProofTree {
    match node {
        MMProofTree::Hyp(i) => MMProofTree::Hyp(*i),
        MMProofTree::Apply {
            assertion,
            subst,
            args,
        } => {
            let new_assertion = float_rename
                .get(assertion)
                .cloned()
                .unwrap_or_else(|| assertion.clone());
            let new_subst = subst
                .iter()
                .map(|(v, toks)| {
                    (
                        *v,
                        toks.iter().map(|t| *code_map.get(t).unwrap_or(t)).collect(),
                    )
                })
                .collect();
            let new_args = args
                .iter()
                .map(|a| rename_tree_dummies(a, code_map, float_rename))
                .collect();
            MMProofTree::Apply {
                assertion: new_assertion,
                subst: new_subst,
                args: new_args,
            }
        }
    }
}

/// A `$d` frame in BOTH `(x,y)` and `(y,x)` orders (deduped) — a verified
/// `$d`-theorem registers its guard hypotheses in both orders, so a reusing proof
/// can discharge whichever order a step needs (`disjPair` is not symmetric).
fn both_orders(pairs: &[(u64, u64)]) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    let mut seen: hashbrown::HashSet<(u64, u64)> = hashbrown::HashSet::new();
    for &(x, y) in pairs {
        for p in [(x, y), (y, x)] {
            if seen.insert(p) {
                out.push(p);
            }
        }
    }
    out
}

/// Apply a token substitution to a formula (used to track stack formulas).
fn instantiate(f: &Formula, subst: &HashMap<String, Vec<String>>) -> Formula {
    let mut tokens = Vec::new();
    for t in &f.tokens {
        if let Some(r) = subst.get(t) {
            tokens.extend(r.iter().cloned());
        } else {
            tokens.push(t.clone());
        }
    }
    Formula {
        typecode: f.typecode.clone(),
        tokens,
    }
}

#[cfg(test)]
#[path = "kernel_verify_tests.rs"]
mod tests;
