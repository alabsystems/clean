// Focused single-constant probe: load a closure, then dump the full type,
// value, and the kernel's inferred type for ONE named constant, so a failing
// check_type can be diagnosed (reconstruction artifact vs genuine kernel gap).
//
// Usage: cargo run --release --example probe_one_430 -- <Const.Name> <Module.Name> <paths...>
use clean_kernel::env::Environment;
use clean_kernel::tc::TypeChecker;
use clean_olean::import::load_module_with_deps;
use std::path::PathBuf;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let target = args.get(1).cloned().unwrap_or_default();
    let module = args.get(2).cloned().unwrap_or_else(|| "Init".to_string());
    let search_paths: Vec<PathBuf> = args.iter().skip(3).map(PathBuf::from).collect();

    let mut env = Environment::default();
    if let Err(e) = load_module_with_deps(&mut env, &module, &search_paths) {
        eprintln!("load failed: {e}");
        std::process::exit(1);
    }
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(0);

    let ci = match env.constants().find(|c| c.name.to_string() == target) {
        Some(c) => c,
        None => {
            eprintln!("constant {target} not found in env");
            std::process::exit(2);
        }
    };
    println!("name   : {}", ci.name);
    println!("kind   : {:?}", ci.kind);
    println!("lvls   : {:?}", ci.level_params);
    println!("TYPE   :\n{:#?}", ci.type_);
    println!("\nVALUE  :\n{:#?}", ci.value);

    println!("\n--- infer_type(type_) ---");
    match tc.infer_type(&ci.type_) {
        Ok(s) => println!("OK sort = {s:?}"),
        Err(e) => println!("ERR {e}"),
    }
    if let Some(val) = &ci.value {
        println!("\n--- infer_type(value) ---");
        match tc.infer_type(val) {
            Ok(inferred) => {
                println!("INFERRED TYPE:\n{inferred:#?}");
                println!("\n--- is_def_eq(inferred, declared type)? ---");
                println!("{}", tc.is_def_eq(&inferred, &ci.type_));
            }
            Err(e) => println!("ERR inferring value type: {e}"),
        }
        println!("\n--- check_type(value, type_) ---");
        match tc.check_type(val, &ci.type_) {
            Ok(()) => println!("CHECK OK"),
            Err(e) => println!("CHECK ERR: {e}"),
        }
    }
}
