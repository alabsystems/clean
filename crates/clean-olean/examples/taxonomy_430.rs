// Mathlib kernel-verification FAILURE TAXONOMY harness.
//
// Loads a dependency-closed module set from a real Lean toolchain lib dir (topo
// order via load_module_with_deps), then kernel-verifies every reconstructed
// constant TWO ways:
//   (1) infer_type(&type_)        -- the declared TYPE is well-formed
//   (2) check_type(&value,&type_) -- the VALUE/PROOF checks against its type
//                                    (this is the *real* kernel verification;
//                                     skipped for axioms/opaque w/ no value)
//
// Every failure is bucketed by KIND of kernel feature it exercises, splitting
// RECONSTRUCTION failures (olean->Expr left a dangling const/var) from genuine
// KERNEL rejections (Expr present, kernel says no). One example name per bucket.
//
// Usage:
//   cargo run --release --example taxonomy_430 -- <lib/lean dir...>=:=<Module.Name> [PREFIX]
// Simpler:
//   cargo run --release --example taxonomy_430 -- <Module.Name> [path1] [path2] ...
// where the LAST args are search-path dirs and the FIRST is the module.
// Optional env: TAXO_PREFIX=Mathlib  restricts the typecheck pass to constants
// whose name starts with that prefix (so Init/Std prelude — already known 100% —
// is excluded from the real-math rate).  TAXO_HB=<n> sets heartbeat limit.

use clean_kernel::env::ConstantKind;
use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::tc::{TypeChecker, TypeError};
use clean_olean::import::load_module_with_deps;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::time::Instant;

/// Coarse failure bucket = (variant tag, reconstruction-vs-kernel).
fn variant_tag(e: &TypeError) -> &'static str {
    match e {
        TypeError::UnboundVariable(_) => "RECON:UnboundVariable",
        TypeError::UnknownFVar(_) => "RECON:UnknownFVar",
        TypeError::UnknownConst(_) => "RECON:UnknownConst",
        TypeError::UnknownInductive(_) => "RECON:UnknownInductive",
        TypeError::NotAFunction { .. } => "KERNEL:NotAFunction",
        TypeError::TypeMismatch { .. } => "KERNEL:TypeMismatch",
        TypeError::ExpectedSort { .. } => "KERNEL:ExpectedSort",
        TypeError::SortDepthExceeded { .. } => "KERNEL:SortDepthExceeded",
        TypeError::InvalidProjNotStruct(_) => "KERNEL:Proj/NotStruct",
        TypeError::InvalidProjNotUniqueConstructor(_) => "KERNEL:Proj/NotUniqueCtor",
        TypeError::InvalidProjIndexOutOfBounds(_, _) => "KERNEL:Proj/IndexOOB",
        TypeError::InvalidProjWrongArgCount { .. } => "KERNEL:Proj/WrongArgCount",
        TypeError::InvalidProjFromProp { .. } => "KERNEL:Proj/FromProp",
        TypeError::ModeRequired { .. } => "KERNEL:ModeRequired",
        TypeError::LevelCountMismatch { .. } => "KERNEL:LevelCountMismatch",
        TypeError::CrossValidationFailure(_) => "KERNEL:CrossValidation",
        TypeError::HeartbeatExceeded { .. } => "LIMIT:Heartbeat",
        TypeError::ExcessiveMemory => "LIMIT:Memory",
        TypeError::DeepRecursion => "LIMIT:DeepRecursion",
        TypeError::Interrupted => "LIMIT:Interrupted",
        TypeError::UndefinedLevelParam { .. } => "KERNEL:UndefinedLevelParam",
        TypeError::UnsafeDeclaration { .. } => "KERNEL:UnsafeDeclaration",
        TypeError::PartialDeclaration { .. } => "KERNEL:PartialDeclaration",
        _ => "OTHER",
    }
}

/// Feature heuristic from the head of an expr's application spine — which kernel
/// feature the failing constant most likely exercises. Best-effort, name-based.
fn feature_of(head: &str) -> &'static str {
    // ordered: most specific first
    if head.starts_with("Quot") || head == "Quotient" || head.starts_with("Quotient.") {
        "quotient (Quot.lift/ind/mk)"
    } else if head.starts_with("WellFounded") || head.contains("wfRec") || head.contains("WfRec") {
        "well-founded recursion (WellFounded.fix)"
    } else if head.starts_with("Acc") {
        "Acc reduction"
    } else if head.contains(".brecOn") || head.contains(".rec") || head.contains(".recAux") {
        "recursor / brecOn unfolding"
    } else if head.starts_with("Decidable")
        || head.contains("decEq")
        || head.contains("instDecidable")
    {
        "Decidable reduction"
    } else if head.starts_with("Nat.")
        || head.starts_with("Int.")
        || head.starts_with("String.")
        || head.starts_with("Char.")
    {
        "native literal / GMP-style reduction"
    } else if head == "OfNat.ofNat" || head.starts_with("OfNat") || head.starts_with("OfScientific")
    {
        "numeric literal (OfNat)"
    } else {
        "other / structure-typeclass"
    }
}

fn head_name(e: &Expr) -> String {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => name.to_string(),
        ExprKind::Sort(_) => "<Sort>".to_string(),
        ExprKind::Pi(_, _, _) => "<Pi>".to_string(),
        ExprKind::Lam(_, _, _) => "<fun>".to_string(),
        ExprKind::Proj(name, idx, _) => format!("<Proj {name}.{idx}>"),
        ExprKind::Lit(_) => "<Lit>".to_string(),
        ExprKind::BVar(i) => format!("<BVar {i}>"),
        ExprKind::Let(..) => "<let>".to_string(),
        _ => "<other>".to_string(),
    }
}

#[derive(Default)]
struct Bucket {
    count: usize,
    by_feature: BTreeMap<&'static str, usize>,
    examples: Vec<(String, String)>, // up to N distinct (const name, short err)
}

fn record(
    map: &mut BTreeMap<&'static str, Bucket>,
    tag: &'static str,
    cname: &str,
    feature: &'static str,
    err: &str,
) {
    let b = map.entry(tag).or_default();
    b.count += 1;
    *b.by_feature.entry(feature).or_default() += 1;
    if b.examples.len() < 8 {
        b.examples
            .push((cname.to_string(), err.chars().take(160).collect()));
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    // first non-flag arg = module; remaining = search paths
    let module = args.get(1).cloned().unwrap_or_else(|| "Init".to_string());
    let search_paths: Vec<PathBuf> = args.iter().skip(2).map(PathBuf::from).collect();
    // TAXO_PREFIX: comma-separated include prefixes (any-match). Empty = all.
    let includes: Vec<String> = std::env::var("TAXO_PREFIX")
        .unwrap_or_default()
        .split(',')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect();
    // TAXO_EXCLUDE: comma-separated exclude prefixes (any-match drops it).
    let excludes: Vec<String> = std::env::var("TAXO_EXCLUDE")
        .unwrap_or_default()
        .split(',')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect();
    let hb: u32 = std::env::var("TAXO_HB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0); // 0 = unlimited
                       // TAXO_MAXVAL: cap on how many constants get the (heavy) value/proof check.
                       // Type-check still runs on all considered constants. 0 = unlimited.
    let max_val: usize = std::env::var("TAXO_MAXVAL")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);

    eprintln!(
        "loading {module} + transitive deps from {:?} ...",
        search_paths
    );
    let t0 = Instant::now();
    let mut env = Environment::default();
    let summaries = match load_module_with_deps(&mut env, &module, &search_paths) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("load_module_with_deps FAILED: {e}");
            std::process::exit(1);
        }
    };
    let modules_loaded = summaries.len();
    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    eprintln!(
        "loaded {modules_loaded} modules, {total_added} consts added, env has {} constants in {:.1}s",
        env.constants().count(),
        t0.elapsed().as_secs_f64()
    );

    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(hb);

    // counters
    let (mut type_pass, mut type_fail) = (0usize, 0usize);
    let (mut val_pass, mut val_fail, mut val_skip) = (0usize, 0usize, 0usize);
    let mut val_over_budget = 0usize;
    let mut considered = 0usize;
    let mut type_buckets: BTreeMap<&'static str, Bucket> = BTreeMap::new();
    let mut val_buckets: BTreeMap<&'static str, Bucket> = BTreeMap::new();
    // kind breakdown of value-checked constants
    let (mut n_def, mut n_thm, mut n_ax, mut n_op) = (0usize, 0usize, 0usize, 0usize);

    let t1 = Instant::now();
    for ci in env.constants() {
        let nm = ci.name.to_string();
        if !includes.is_empty() && !includes.iter().any(|p| nm.starts_with(p)) {
            continue;
        }
        if excludes.iter().any(|p| nm.starts_with(p)) {
            continue;
        }
        considered += 1;
        match ci.kind {
            ConstantKind::Definition => n_def += 1,
            ConstantKind::Theorem => n_thm += 1,
            ConstantKind::Axiom => n_ax += 1,
            ConstantKind::Opaque => n_op += 1,
        }

        // (1) TYPE well-formedness
        tc.reset_heartbeat();
        match tc.infer_type(&ci.type_) {
            Ok(_) => type_pass += 1,
            Err(e) => {
                type_fail += 1;
                let tag = variant_tag(&e);
                let feat = feature_of(&head_name(&ci.type_));
                record(&mut type_buckets, tag, &nm, feat, &format!("{e}"));
            }
        }

        // (2) VALUE/PROOF checks against declared type (the real kernel verify)
        let val_budget_ok = max_val == 0 || (val_pass + val_fail) < max_val;
        match &ci.value {
            Some(val) if val_budget_ok => {
                tc.reset_heartbeat();
                match tc.check_type(val, &ci.type_) {
                    Ok(()) => val_pass += 1,
                    Err(e) => {
                        val_fail += 1;
                        let tag = variant_tag(&e);
                        let feat = feature_of(&head_name(val));
                        record(&mut val_buckets, tag, &nm, feat, &format!("{e}"));
                    }
                }
            }
            Some(_) => val_over_budget += 1, // value-bearing but past TAXO_MAXVAL cap
            None => val_skip += 1,
        }
    }
    let verify_secs = t1.elapsed().as_secs_f64();

    let pct = |a: usize, b: usize| {
        if b > 0 {
            100.0 * a as f64 / b as f64
        } else {
            0.0
        }
    };

    println!("\n================ taxonomy_430 ================");
    println!("module          : {module}");
    println!("include prefixes: {includes:?}   exclude prefixes: {excludes:?}");
    println!("modules loaded  : {modules_loaded}");
    println!("env constants   : {}", env.constants().count());
    println!("considered      : {considered}  (Def {n_def} / Thm {n_thm} / Axiom {n_ax} / Opaque {n_op})");
    println!("verify wall time: {verify_secs:.1}s");
    println!();
    println!("--- (1) TYPE well-formedness: infer_type(type_) ---");
    println!(
        "  PASS {type_pass}  FAIL {type_fail}  rate {:.3}%",
        pct(type_pass, type_pass + type_fail)
    );
    println!("--- (2) VALUE/PROOF check: check_type(value, type_) ---");
    println!("  PASS {val_pass}  FAIL {val_fail}  SKIP(no value: axiom/opaque) {val_skip}  OVER-BUDGET {val_over_budget}");
    println!(
        "  rate over value-bearing consts: {:.3}%",
        pct(val_pass, val_pass + val_fail)
    );

    let dump = |label: &str, m: &BTreeMap<&'static str, Bucket>, total: usize| {
        println!("\n### {label} failure taxonomy (total {total}) ###");
        // sort buckets by count desc
        let mut v: Vec<_> = m.iter().collect();
        v.sort_by_key(|e| std::cmp::Reverse(e.1.count));
        for (tag, b) in v {
            println!("  {:>7}  {}", b.count, tag);
            let mut fv: Vec<_> = b.by_feature.iter().collect();
            fv.sort_by(|a, b| b.1.cmp(a.1));
            for (feat, n) in fv.iter().take(4) {
                println!("            {n:>7}  feature: {feat}");
            }
            for (cn, er) in &b.examples {
                println!("            e.g. {cn}");
                println!("                 -> {er}");
            }
        }
    };
    dump("TYPE-CHECK", &type_buckets, type_fail);
    dump("VALUE/PROOF-CHECK", &val_buckets, val_fail);
}
