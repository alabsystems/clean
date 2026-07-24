// Audit probe (lane B, 2026-07-09): load a real toolchain module into a kernel
// Environment through the production import path and report what
// extension-derived elaboration state actually got restored:
// instance table, class table (out_params), reducibility, simp lemmas.
//
// Usage: cargo run -p clean-olean --example probe_env_state -- <module> [search_path]
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let module = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| "Init.Prelude".into());
    let search = args.get(2).cloned().unwrap_or_else(|| {
        let home = std::env::var("HOME").expect("HOME");
        format!("{home}/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean")
    });

    let mut env = Environment::new();
    let summaries =
        load_module_with_deps(&mut env, &module, &[search.into()]).expect("load module");
    let added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "loaded {module}: {} modules, {added} constants",
        summaries.len()
    );

    // 1. Instance table: what does resolve_instance see?
    for class in ["HAdd", "OfNat", "Decidable", "Membership", "BEq"] {
        let cname = Name::interned(class);
        let insts = env.get_class_instances(&cname);
        println!(
            "class {class:12} is_class={} out_params={:?} instances={}",
            env.is_class(&cname),
            env.get_class_info(&cname).map(|c| c.out_params.clone()),
            insts.len()
        );
        for i in insts.iter().take(4) {
            println!("    {} (priority {})", i.name, i.priority);
        }
    }

    // 2. Specific instances Lean marks @[instance] — and one Lean does NOT.
    for inst in [
        "instHAdd",   // real @[instance] (priority 1000 wrapper)
        "instAddNat", // real @[instance]
        "instDecidableNot",
        "Nat.decEq",  // NOT @[instance] in Lean (instDecidableEqNat wraps it)
        "Bool.decEq", // NOT @[instance] in Lean
    ] {
        let n = Name::interned(inst);
        println!("is_instance({inst}) = {}", env.is_instance(&n));
    }

    // 3. Reducibility of imported defs (reducibilityCore ground truth:
    //    UInt8.recOn / Membership.casesOn are @[reducible] in the olean).
    for c in [
        "UInt8.recOn",
        "Membership.casesOn",
        "Function.comp",
        "instHAdd",
        "Nat.add",
    ] {
        let n = Name::interned(c);
        println!(
            "reducibility({c}) = {:?} (hints abbrev? {:?})",
            env.get_reducibility(&n),
            env.get_const(&n).map(|ci| ci.is_reducible)
        );
    }

    // 4. Instance-table size vs ground truth (Prelude olean carries 151
    //    instanceExtension entries; the heuristic registers by type shape).
    let mut classes = std::collections::HashSet::new();
    let mut total_instances = 0usize;
    for c in env.constants().map(|c| c.name.clone()).collect::<Vec<_>>() {
        if env.is_instance(&c) {
            total_instances += 1;
        }
        if env.is_class(&c) {
            classes.insert(c);
        }
    }
    println!(
        "registered classes (owned-constant names only): {}",
        classes.len()
    );
    println!("registered instances (owned-constant names only): {total_instances}");
}
