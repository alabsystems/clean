// NY -> Clean Propose->Trust bridge harness.
//
// IMPORTS the NY proof-carrying-verification soundness theorems (proven in
// Lean, compiled to .olean) into Clean's small-TCB kernel via clean-olean, and
// confirms Clean's kernel INDEPENDENTLY RE-TYPECHECKS them.
//
// For each requested theorem we assert, machine-checked:
//   1. the imported Declaration is PRESENT in the kernel Environment,
//   2. kernel infer_type(type_) Ok          (the *statement* is well-formed),
//   3. kernel infer_type(value) Ok AND is_def_eq(inferred, declared)
//      (the kernel re-checks the *proof term* against the stated type),
//   4. !has_sorry: trace_sorry_deps(name) is empty (no sorry/sorryAx leak).
//
// Usage:
//   ny_bridge <CROWNPROOF_OLEAN_DIR> <SEARCH_PATH>... -- <Module> <Const>...
// or with built-in Q-core module/theorem list when no `--` args are given.

use std::collections::HashSet;
use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;

use clean_kernel::env::{is_foundational_axiom, Environment};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_kernel::ConstantKind;
use clean_olean::{load_module_with_deps, LoadSummary};

/// Collect every `Const` name referenced anywhere in `expr` (iterative).
fn collect_const_refs(expr: &Expr, out: &mut Vec<Name>) {
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(name, _) => out.push(name.clone()),
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            _ => {}
        }
    }
}

/// Targeted, scalable sorry-freeness check: transitive-closure walk from
/// `root` over only the constants actually reachable from its type+value,
/// flagging any reached declaration that is a sorry/sorryAx axiom or a
/// non-foundational axiom (an unproved obligation). This is O(reachable
/// subgraph) rather than O(whole environment) — the full-environment
/// SorryTracer does not scale to a mathlib closure (~270k consts).
///
/// Returns the list of distinct sorry/obligation axiom names reached.
fn reachable_sorry_axioms(env: &Environment, root: &Name) -> Vec<String> {
    let mut visited: HashSet<Name> = HashSet::new();
    let mut worklist: Vec<Name> = vec![root.clone()];
    let mut sorry_found: HashSet<String> = HashSet::new();

    while let Some(name) = worklist.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        let Some(ci) = env.get_const(&name) else {
            continue;
        };
        // Classify axioms.
        if ci.kind == ConstantKind::Axiom {
            let nm = name.to_string();
            if nm.contains("sorry") || nm.contains("Sorry") {
                sorry_found.insert(nm);
            } else if !is_foundational_axiom(&name) {
                // Non-foundational axiom = unproved domain obligation.
                sorry_found.insert(format!("{nm} (non-foundational axiom)"));
            }
        }
        let mut refs = Vec::new();
        collect_const_refs(&ci.type_, &mut refs);
        if let Some(ref v) = ci.value {
            collect_const_refs(v, &mut refs);
        }
        for r in refs {
            if !visited.contains(&r) {
                worklist.push(r);
            }
        }
    }

    let mut v: Vec<String> = sorry_found.into_iter().collect();
    v.sort();
    v
}

/// Print + flush immediately so progress survives a crash / kill.
macro_rules! log {
    ($($arg:tt)*) => {{
        println!($($arg)*);
        let _ = std::io::stdout().flush();
    }};
}

/// (Crownproof module to load, theorems within it to re-typecheck).
/// Each module's load pulls its full transitive import closure (incl. mathlib).
fn qcore_plan() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("Crownproof.Basic", vec!["Crownproof.farkas_comb"]),
        (
            "Crownproof.Bridge",
            vec![
                "Crownproof.farkas_premise_combination",
                "Crownproof.crown_bridge",
            ],
        ),
        ("Crownproof.CertEquiv", vec!["Crownproof.cert_list_sound"]),
        ("Crownproof.Branch", vec!["Crownproof.branch_split_min"]),
        ("Crownproof.Sbar", vec!["Crownproof.sbar_support_sound"]),
        (
            "Crownproof.MultiHead",
            vec!["Crownproof.multihead_support_sound"],
        ),
        (
            "Crownproof.SoftmaxOp",
            vec!["Crownproof.softmax_barycentric"],
        ),
        ("Crownproof.DeepK", vec!["Crownproof.crown_bridge_deepK"]),
        // Quadric (geo_conform) certificate envelopes: tangent/secant linear
        // relaxations of s = t^2 over Q — the premise classes NY's quadric
        // ground-truth certifier emits (sphere/cylinder/cone residuals).
        (
            "Crownproof.Pow2Envelope",
            vec!["Crownproof.pow2_tangent", "Crownproof.pow2_secant"],
        ),
        ("Crownproof.LayerNorm", vec!["Crownproof.layernorm_bridge"]),
        ("Crownproof.Block", vec!["Crownproof.block_bridge"]),
        ("Crownproof.Network", vec!["Crownproof.network_bridge"]),
    ]
}

struct TheoremResult {
    name: String,
    present: bool,
    type_ok: bool,
    value_ok: bool,
    def_eq: bool,
    has_value: bool,
    sorry_deps: usize,
    detail: String,
}

fn check_theorem(env: &Environment, full_name: &str) -> TheoremResult {
    let name = Name::from_string(full_name);
    let mut r = TheoremResult {
        name: full_name.to_string(),
        present: false,
        type_ok: false,
        value_ok: false,
        def_eq: false,
        has_value: false,
        sorry_deps: 0,
        detail: String::new(),
    };

    let Some(ci) = env.get_const(&name) else {
        r.detail = "NOT FOUND in imported environment".to_string();
        return r;
    };
    r.present = true;
    let ci_type = ci.type_.clone();
    let ci_value = ci.value.clone();
    r.has_value = ci_value.is_some();

    // (2) re-typecheck the STATEMENT. catch_unwind localises any kernel panic
    // (e.g. stack overflow surrogate) to this theorem instead of killing the run.
    log!("      . infer_type(type_) ...");
    let stmt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let tc = TypeChecker::new(env);
        tc.infer_type(&ci_type)
    }));
    match stmt {
        Ok(Ok(_)) => r.type_ok = true,
        Ok(Err(e)) => {
            r.detail = format!("infer_type(type_) error: {e:?}");
            return r;
        }
        Err(_) => {
            r.detail = "PANIC during infer_type(type_)".to_string();
            return r;
        }
    }

    // (3) re-typecheck the PROOF TERM against the stated type.
    if let Some(value) = ci_value {
        log!("      . infer_type(value) ...");
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let tc = TypeChecker::new(env);
            let inferred = tc.infer_type(&value)?;
            let tc2 = TypeChecker::new(env);
            let eq = tc2.is_def_eq(&inferred, &ci_type);
            Ok::<bool, clean_kernel::tc::TypeError>(eq)
        }));
        match res {
            Ok(Ok(eq)) => {
                r.value_ok = true;
                r.def_eq = eq;
                if !eq {
                    r.detail = "proof term type != stated type".to_string();
                }
            }
            Ok(Err(e)) => {
                r.detail = format!("infer_type(value) error: {e:?}");
            }
            Err(_) => {
                r.detail = "PANIC during infer_type(value)".to_string();
            }
        }
    } else {
        r.detail = "no proof term (axiom/opaque) -- statement-only".to_string();
    }

    r
}

fn main() -> ExitCode {
    // Kernel infer_type over fully-elaborated mathlib proof terms can recurse
    // deeply; run on a thread with a large (1 GiB) stack so deep but legitimate
    // proof terms do not overflow the default 8 MiB main-thread stack.
    let handle = std::thread::Builder::new()
        .name("ny_bridge".to_string())
        .stack_size(1024 * 1024 * 1024)
        .spawn(run)
        .expect("spawn worker thread");
    match handle.join() {
        Ok(code) => code,
        Err(_) => {
            eprintln!("worker thread panicked");
            ExitCode::from(70)
        }
    }
}

fn run() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!(
            "usage: {} <SEARCH_PATH>...  [-- <Module> <Const>...]",
            args[0]
        );
        return ExitCode::from(2);
    }

    // Split on `--`: before = search paths, after = optional explicit module+consts.
    let mut search_paths: Vec<PathBuf> = Vec::new();
    let mut explicit: Vec<String> = Vec::new();
    let mut after = false;
    for a in &args[1..] {
        if a == "--" {
            after = true;
            continue;
        }
        if after {
            explicit.push(a.clone());
        } else {
            search_paths.push(PathBuf::from(a));
        }
    }

    let plan: Vec<(String, Vec<String>)> = if explicit.is_empty() {
        qcore_plan()
            .into_iter()
            .map(|(m, ts)| {
                (
                    m.to_string(),
                    ts.into_iter().map(|s| s.to_string()).collect(),
                )
            })
            .collect()
    } else {
        let module = explicit[0].clone();
        let consts = explicit[1..].to_vec();
        vec![(module, consts)]
    };

    log!("=== NY -> Clean Propose->Trust bridge ===");
    log!("search paths ({}):", search_paths.len());
    for p in &search_paths {
        log!("  {}", p.display());
    }

    // Single shared Environment: load each module's closure once, dedup across
    // modules. The kernel re-typechecks every constant as it is registered by
    // clean-olean's loader, then we additionally re-run infer_type below.
    let mut env = Environment::default();
    let mut total_added: usize = 0;
    let mut total_skipped: usize = 0;
    let mut all_skips: Vec<(String, String)> = Vec::new();

    let mut all_results: Vec<TheoremResult> = Vec::new();
    // (module, const) pairs we successfully reached, for the final sorry pass.
    let mut to_sorry_check: Vec<usize> = Vec::new();

    for (module, consts) in &plan {
        let t0 = std::time::Instant::now();
        log!("\n>>> loading {module} ...");
        let summaries: Vec<LoadSummary> =
            match load_module_with_deps(&mut env, module, &search_paths) {
                Ok(s) => s,
                Err(e) => {
                    log!("LOAD ERROR: {e:?}");
                    for c in consts {
                        all_results.push(TheoremResult {
                            name: c.clone(),
                            present: false,
                            type_ok: false,
                            value_ok: false,
                            def_eq: false,
                            has_value: false,
                            sorry_deps: 0,
                            detail: format!("module load failed: {e:?}"),
                        });
                    }
                    continue;
                }
            };
        let added: usize = summaries.iter().map(|s| s.added_constants).sum();
        let skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();
        for s in &summaries {
            for sk in &s.skipped_constants {
                all_skips.push((sk.name.clone(), sk.reason.clone()));
            }
        }
        total_added += added;
        total_skipped += skipped;
        log!(
            ">>> {module}: added={added} skipped={skipped} (env total constants now {}) [{:.1}s]",
            env.constants().count(),
            t0.elapsed().as_secs_f64()
        );

        for c in consts {
            log!("  -- re-typechecking {c} ...");
            let tc0 = std::time::Instant::now();
            let r = check_theorem(&env, c);
            // sorry-freeness is computed in a single batched pass after all
            // loads (building a tracer per theorem over ~270k consts is wasteful).
            let verdict = if r.present && r.type_ok && (!r.has_value || (r.value_ok && r.def_eq)) {
                "kernel infer_type OK (sorry pass pending)"
            } else {
                "FAILED"
            };
            log!(
                "    [{verdict}] {}  present={} type_ok={} has_value={} value_ok={} def_eq={} [{:.1}s]{}",
                r.name,
                r.present,
                r.type_ok,
                r.has_value,
                r.value_ok,
                r.def_eq,
                tc0.elapsed().as_secs_f64(),
                if r.detail.is_empty() {
                    String::new()
                } else {
                    format!("  -- {}", r.detail)
                }
            );
            to_sorry_check.push(all_results.len());
            all_results.push(r);
        }
    }

    // (4) Sorry-freeness: targeted transitive-closure walk per theorem over its
    // own reachable constant subgraph (O(reachable), scales to mathlib).
    log!("\n>>> sorry-freeness: per-theorem reachable-axiom walk ...");
    for &idx in &to_sorry_check {
        if !all_results[idx].present {
            continue;
        }
        let nm = Name::from_string(&all_results[idx].name);
        let s0 = std::time::Instant::now();
        let walk = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            reachable_sorry_axioms(&env, &nm)
        }));
        match walk {
            Ok(deps) => {
                all_results[idx].sorry_deps = deps.len();
                log!(
                    "    sorry/obligation axioms reachable from {} = {} [{:.1}s]{}",
                    all_results[idx].name,
                    deps.len(),
                    s0.elapsed().as_secs_f64(),
                    if deps.is_empty() {
                        String::new()
                    } else {
                        format!("  {:?}", &deps[..deps.len().min(8)])
                    }
                );
            }
            Err(_) => {
                all_results[idx].sorry_deps = usize::MAX; // mark as failed
                all_results[idx].detail = "PANIC during sorry walk".to_string();
                log!("    PANIC during sorry walk for {}", all_results[idx].name);
            }
        }
    }

    // Summary.
    log!("\n=== LoadSummary (aggregate over all loaded modules) ===");
    log!("added_constants  = {total_added}");
    log!("skipped_constants = {total_skipped}");
    if !all_skips.is_empty() {
        // dedup skip reasons
        all_skips.sort();
        all_skips.dedup();
        log!("distinct skipped constants ({}):", all_skips.len());
        for (n, why) in all_skips.iter().take(50) {
            log!("  SKIP {n}: {why}");
        }
    }

    log!("\n=== Theorem re-typecheck verdicts ===");
    let mut ok = 0;
    let mut fail = 0;
    for r in &all_results {
        let pass = r.present
            && r.type_ok
            && (!r.has_value || (r.value_ok && r.def_eq))
            && r.sorry_deps == 0;
        if pass {
            ok += 1;
        } else {
            fail += 1;
        }
        log!("  {} {}", if pass { "PASS" } else { "FAIL" }, r.name);
    }
    log!(
        "\nRESULT: {ok}/{} Q-core theorems re-typechecked in Clean's kernel ({fail} failed).",
        all_results.len()
    );

    if fail == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}
