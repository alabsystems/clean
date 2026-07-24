// Kernel-correctness check: load a dependency-closed module set from a real
// Lean toolchain lib dir, then typecheck every reconstructed constant's type
// through the clean kernel. A wrong base_addr would reconstruct garbage Exprs
// that the kernel rejects; clean passes prove the reconstruction is faithful.
//
// Usage: cargo run --release --example kverify_430 -- <lib/lean dir> <Module.Name>
use clean_kernel::env::Environment;
use clean_kernel::tc::TypeChecker;
use clean_olean::import::load_module_with_deps;
use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let lib = PathBuf::from(args.get(1).cloned().unwrap_or_default());
    let module = args.get(2).cloned().unwrap_or_else(|| "Init".to_string());

    let mut env = Environment::default();
    let summaries = match load_module_with_deps(&mut env, &module, std::slice::from_ref(&lib)) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("load_module_with_deps FAILED: {e}");
            std::process::exit(1);
        }
    };
    let modules_loaded = summaries.len();
    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();

    let tc = TypeChecker::new(&env);
    let (mut pass, mut fail) = (0usize, 0usize);
    let mut sample_fail: Vec<String> = Vec::new();
    for ci in env.constants() {
        match tc.infer_type(&ci.type_) {
            Ok(_) => pass += 1,
            Err(e) => {
                fail += 1;
                if sample_fail.len() < 10 {
                    sample_fail.push(format!("{}: {:?}", ci.name, e));
                }
            }
        }
    }

    println!("=== kverify_430 ===");
    println!("lib      : {}", lib.display());
    println!("module   : {module}");
    println!("modules loaded (with deps): {modules_loaded}");
    println!("constants registered      : {total_added}");
    println!("env constant count        : {}", env.constants().count());
    println!("kernel typecheck PASS     : {pass}");
    println!("kernel typecheck FAIL     : {fail}");
    let denom = pass + fail;
    if denom > 0 {
        println!(
            "PASS rate                 : {:.2}%",
            100.0 * pass as f64 / denom as f64
        );
    }
    for s in &sample_fail {
        println!("  fail sample: {}", s.chars().take(160).collect::<String>());
    }
}
