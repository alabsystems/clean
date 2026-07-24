// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Residual-MATH bucket dissector.
//!
//! Loads ONE module's transitive olean closure into a fresh import prelude env
//! (exactly like the sharded verify worker), then for each requested constant
//! dumps the kernel's view: declared type, value's inferred type, the WHNF of
//! both sides at the head, the level-param list, and an `is_def_eq` verdict
//! between declared type and inferred type.
//!
//! This is a DIAGNOSTIC tool for the deep-reducers investigation — it is not
//! part of any trust path and modifies no environment. It exists so the next
//! agent can re-probe the four residual-MATH buckets after a candidate fix.
//!
//! Usage:
//!   mathverse_bucket_probe --module <M> [--olean-root R]... -- <const> [<const>...]

use std::path::PathBuf;

use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_kernel::{Declaration, TransparencyMode};
use clean_olean::load_module_with_deps;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut module = String::new();
    let mut roots: Vec<PathBuf> = Vec::new();
    let mut consts: Vec<String> = Vec::new();
    let mut after_sep = false;
    let mut i = 1;
    while i < args.len() {
        let a = &args[i];
        if after_sep {
            consts.push(a.clone());
            i += 1;
            continue;
        }
        match a.as_str() {
            "--module" => {
                module = args.get(i + 1).cloned().unwrap_or_default();
                i += 2;
            }
            "--olean-root" => {
                if let Some(r) = args.get(i + 1) {
                    roots.push(PathBuf::from(r));
                }
                i += 2;
            }
            "--" => {
                after_sep = true;
                i += 1;
            }
            other => {
                eprintln!("unknown arg: {other}");
                i += 1;
            }
        }
    }

    if module.is_empty() || consts.is_empty() {
        eprintln!("usage: mathverse_bucket_probe --module <M> [--olean-root R]... -- <const>...");
        std::process::exit(2);
    }

    let mut env = match Environment::try_with_prelude_for_import() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("prelude build failed: {e}");
            std::process::exit(1);
        }
    };
    eprintln!("[probe] loading {module} + deps ...");
    if let Err(e) = load_module_with_deps(&mut env, &module, &roots) {
        eprintln!("load failed: {e}");
        std::process::exit(1);
    }
    eprintln!("[probe] closure constants: {}", env.num_constants());

    for cname in &consts {
        probe_one(&env, cname);
    }
}

fn short(e: &Expr) -> String {
    // A compact head-oriented rendering so the dumps fit on a screen.
    let s = format!("{:?}", e);
    if s.len() > 4000 {
        format!("{}…[{} chars]", &s[..4000], s.len())
    } else {
        s
    }
}

fn head_const(e: &Expr) -> String {
    let h = e.get_app_fn();
    match h.kind() {
        ExprKind::Const(n, lv) => format!("Const {} (levels={})", n, lv.len()),
        ExprKind::Proj(ind, idx, _) => format!("Proj {}.{}", ind, idx),
        ExprKind::Sort(l) => format!("Sort({:?})", l),
        ExprKind::Pi(..) => "Pi".to_string(),
        ExprKind::Lam(..) => "Lam".to_string(),
        ExprKind::FVar(id) => format!("FVar({:?})", id),
        ExprKind::BVar(i) => format!("BVar({i})"),
        other => format!("{:?}-head", std::mem::discriminant(other)),
    }
}

fn probe_one(env: &Environment, cname: &str) {
    println!("\n================ PROBE {cname} ================");
    let kname = Name::from_string(cname);
    let Some(ci) = env.get_const(&kname) else {
        println!("  NOT FOUND in env");
        return;
    };
    println!("  kind          : {:?}", ci.kind);
    println!(
        "  level_params  : {:?} (n={})",
        ci.level_params,
        ci.level_params.len()
    );
    println!("  declared type head: {}", head_const(&ci.type_));
    println!("  declared type : {}", short(&ci.type_));

    let tc = TypeChecker::new(env);

    // Sort of the declared type (the type-of-type check).
    match tc.infer_sort(&ci.type_) {
        Ok(s) => println!("  infer_sort(type) = {:?}", s),
        Err(e) => println!("  infer_sort(type) ERR: {e:?}"),
    }

    let Some(value) = &ci.value else {
        println!("  (no value — axiom/opaque)");
        return;
    };
    println!("  value head    : {}", head_const(value));
    if std::env::var("PROBE_DUMP_VALUE").is_ok() {
        println!("  value         : {}", short(value));
    }

    // Infer the type of the value, then compare against the declared type.
    match tc.infer_type(value) {
        Ok(inferred) => {
            println!("  inferred type head: {}", head_const(&inferred));
            println!("  inferred type : {}", short(&inferred));

            // WHNF both sides — this is where the stuck reduction shows up.
            let dt_whnf = tc.whnf(&ci.type_);
            let it_whnf = tc.whnf(&inferred);
            println!("  whnf(declared) head: {}", head_const(&dt_whnf));
            println!("  whnf(inferred) head: {}", head_const(&it_whnf));

            // WHNF with ALL transparency (force delta on instances/projections).
            let dt_all = tc.whnf_with_transparency(&ci.type_, TransparencyMode::All);
            let it_all = tc.whnf_with_transparency(&inferred, TransparencyMode::All);
            println!("  whnf-ALL(declared) head: {}", head_const(&dt_all));
            println!("  whnf-ALL(inferred) head: {}", head_const(&it_all));

            let deq = tc.is_def_eq(&ci.type_, &inferred);
            println!("  is_def_eq(declared, inferred) = {deq}");

            // Now check_type to surface the exact failure with its location.
            match tc.check_type(value, &ci.type_) {
                Ok(()) => println!("  check_type: OK"),
                Err(e) => println!("  check_type ERR: {e:?}"),
            }
        }
        Err(e) => {
            println!("  infer_type(value) ERR: {e:?}");
            match tc.check_type(value, &ci.type_) {
                Ok(()) => println!("  check_type: OK"),
                Err(ce) => println!("  check_type ERR: {ce:?}"),
            }
        }
    }

    // If declared type is `@C.proj self`-headed or contains a projection that
    // stays stuck, also dump the underlying Declaration to inspect levels.
    if let Some(Declaration::Definition { level_params, .. })
    | Some(Declaration::Theorem { level_params, .. }) = env_decl(env, &kname)
    {
        let _ = level_params; // (already printed above; placeholder for symmetry)
    }
}

fn env_decl(env: &Environment, name: &Name) -> Option<Declaration> {
    let ci = env.get_const(name)?;
    let lp = ci.level_params.clone();
    Some(match ci.kind {
        clean_kernel::ConstantKind::Theorem => Declaration::Theorem {
            name: name.clone(),
            level_params: lp,
            type_: ci.type_.clone(),
            value: ci.value.clone()?,
        },
        _ => Declaration::Definition {
            name: name.clone(),
            level_params: lp,
            type_: ci.type_.clone(),
            value: ci.value.clone()?,
            is_reducible: ci.is_reducible,
        },
    })
}
