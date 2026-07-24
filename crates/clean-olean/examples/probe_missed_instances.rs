// Audit probe (lane B): which real `@[instance]` entries would the shape
// heuristic (`valid_instance_class`) have dropped? These are the instances
// that were entirely ABSENT from the table before the typed decoder.
// Usage: cargo run -p clean-olean --example probe_missed_instances -- <file.olean>
use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::name::Name;
use clean_olean::import::parse_module;
use clean_olean::{load_module_with_deps, ParsedExtensionEntry};

fn mentions_bvar(expr: &Expr, target: u32) -> bool {
    match expr.kind() {
        ExprKind::BVar(idx) => *idx == target,
        ExprKind::App(f, a) => mentions_bvar(f, target) || mentions_bvar(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_bvar(ty, target) || mentions_bvar(body, target + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_bvar(ty, target)
                || mentions_bvar(val, target)
                || mentions_bvar(body, target + 1)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => mentions_bvar(inner, target),
        _ => false,
    }
}

// Mirror of load_register::valid_instance_class
fn valid_instance_class(ty: &Expr) -> Option<Name> {
    let mut binders: Vec<(BinderInfo, Expr)> = Vec::new();
    let mut conclusion = ty;
    while let ExprKind::Pi(bd, bty, body) = conclusion.kind() {
        binders.push((bd.info, (**bty).clone()));
        conclusion = body;
    }
    let class = match conclusion.get_app_fn().kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => return None,
    };
    let n = binders.len();
    for (p, (info, bty)) in binders.iter().enumerate() {
        if *info == BinderInfo::Default
            && !mentions_bvar(conclusion, (n - 1 - p) as u32)
            && !matches!(bty.get_app_fn().kind(), ExprKind::Const(..))
        {
            return None;
        }
    }
    Some(class)
}

fn main() {
    let path = std::env::args().nth(1).expect("olean path");
    let bytes = std::fs::read(&path).expect("read");
    let m = parse_module(&bytes).expect("parse");
    let home = std::env::var("HOME").expect("HOME");
    let search = format!("{home}/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean");
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[search.into()]).expect("load");
    for ext in &m.entries {
        if ext.extension_name != "Lean.Meta.instanceExtension" {
            continue;
        }
        for e in &ext.entries {
            if let ParsedExtensionEntry::Instance(inst) = e {
                let n = Name::interned(&inst.instance_name);
                let verdict = match env.get_const(&n) {
                    None => "NO-CONST",
                    Some(c) => match (c.kind, valid_instance_class(&c.type_)) {
                        (_, None) => "HEURISTIC-DROPPED",
                        (clean_kernel::env::ConstantKind::Definition, Some(_))
                        | (clean_kernel::env::ConstantKind::Theorem, Some(_)) => "ok",
                        _ => "KIND-DROPPED",
                    },
                };
                if verdict != "ok" {
                    println!(
                        "{verdict:18} {} (prio {}, {:?})",
                        inst.instance_name, inst.priority, inst.attr_kind
                    );
                }
            }
        }
    }
}
