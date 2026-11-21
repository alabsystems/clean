// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The adders under test, a verbatim copier of `Environment::with_prelude()`
//! closures and a transcription of the shortcut's reconstruction, for
//! `parity_forged_eq_known_gap.rs`.

use std::collections::HashSet;

use clean_kernel::env::KernelTheory;
use clean_kernel::{
    BinderInfo, ConstantKind, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, Name, ReferenceKernel,
};

/// The two adders under test: the plain environment (the re-check lanes'
/// `add_decl`/`add_inductive_core`) and the fenced reference entry.
pub(crate) trait Sink {
    fn env(&self) -> &Environment;
    fn add(&mut self, d: Declaration) -> Result<(), String>;
    fn add_ind(&mut self, d: InductiveDecl) -> Result<(), String>;
}

impl Sink for Environment {
    fn env(&self) -> &Environment {
        self
    }
    fn add(&mut self, d: Declaration) -> Result<(), String> {
        self.add_decl(d).map_err(|e| e.to_string())
    }
    fn add_ind(&mut self, d: InductiveDecl) -> Result<(), String> {
        self.add_inductive_core(d).map_err(|e| e.to_string())
    }
}

impl Sink for ReferenceKernel {
    fn env(&self) -> &Environment {
        self.environment()
    }
    fn add(&mut self, d: Declaration) -> Result<(), String> {
        self.add_checked(d).map(|_| ()).map_err(|e| e.to_string())
    }
    fn add_ind(&mut self, d: InductiveDecl) -> Result<(), String> {
        self.add_inductive_checked(d)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
}

/// Every kernel the gap was measured in.
pub(crate) fn kernels() -> Vec<(String, Box<dyn Sink>)> {
    let mut out: Vec<(String, Box<dyn Sink>)> = Vec::new();
    for theory in [
        KernelTheory::Extended,
        KernelTheory::Lean,
        KernelTheory::LeanReference,
    ] {
        let mut env = Environment::for_lean_replay();
        env.set_kernel_theory(theory);
        out.push((format!("for_lean_replay under {theory:?}"), Box::new(env)));
    }
    let entry = ReferenceKernel::new(Environment::for_lean_replay())
        .expect("the fenced entry starts from for_lean_replay");
    out.push((
        "ReferenceKernel over for_lean_replay".into(),
        Box::new(entry),
    ));
    out
}

// ---------------------------------------------------------------------------
// Copy a dependency closure out of `Environment::with_prelude()`, verbatim.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Unit {
    Block(Name),
    Decl(Name),
}

fn block_head(src: &Environment, ind: &Name) -> Name {
    src.get_inductive(ind)
        .map_or_else(|| ind.clone(), |i| i.all_names[0].clone())
}

fn unit_of(src: &Environment, name: &Name) -> Unit {
    if src.get_inductive(name).is_some() {
        Unit::Block(block_head(src, name))
    } else if let Some(ctor) = src.get_constructor(name) {
        Unit::Block(block_head(src, &ctor.inductive_name))
    } else if let Some(rec) = src.get_recursor(name) {
        Unit::Block(block_head(src, &rec.inductive_name))
    } else {
        Unit::Decl(name.clone())
    }
}

fn block_decl(src: &Environment, head: &Name) -> (InductiveDecl, HashSet<Name>) {
    let first = src.get_inductive(head).expect("inductive head");
    let mut members = HashSet::new();
    let mut deps = HashSet::new();
    let mut types = Vec::new();
    for type_name in &first.all_names {
        let ind = src.get_inductive(type_name).expect("block member");
        members.insert(type_name.clone());
        deps.extend(ind.type_.collect_constants());
        let mut constructors = Vec::new();
        for ctor_name in &ind.constructor_names {
            let ctor = src.get_constructor(ctor_name).expect("constructor");
            members.insert(ctor_name.clone());
            deps.extend(ctor.type_.collect_constants());
            constructors.push(Constructor {
                name: ctor_name.clone(),
                type_: ctor.type_.clone(),
            });
        }
        types.push(InductiveType {
            name: type_name.clone(),
            type_: ind.type_.clone(),
            constructors,
        });
    }
    deps.retain(|d| !members.contains(d));
    let decl = InductiveDecl {
        level_params: first.level_params.clone(),
        num_params: first.num_params,
        types,
    };
    (decl, deps)
}

fn unit_deps(src: &Environment, unit: &Unit) -> HashSet<Name> {
    match unit {
        Unit::Block(head) => block_decl(src, head).1,
        Unit::Decl(name) => {
            let info = src.get_const(name).expect("closure member");
            let mut deps = info.type_.collect_constants();
            if let Some(value) = &info.value {
                deps.extend(value.collect_constants());
            }
            deps.into_iter().filter(|d| d != name).collect()
        }
    }
}

/// Post-order over the closure of `roots`, so each unit follows its deps.
fn closure_order(src: &Environment, roots: &[&str]) -> Vec<Unit> {
    let mut visited = HashSet::new();
    let mut order = Vec::new();
    let mut stack: Vec<(Unit, bool)> = roots
        .iter()
        .rev()
        .map(|r| (unit_of(src, &Name::from_string(r)), false))
        .collect();
    while let Some((unit, expanded)) = stack.pop() {
        if expanded {
            order.push(unit);
            continue;
        }
        if !visited.insert(unit.clone()) {
            continue;
        }
        stack.push((unit.clone(), true));
        let mut deps: Vec<Name> = unit_deps(src, &unit).into_iter().collect();
        deps.sort_by_cached_key(ToString::to_string);
        for dep in deps {
            assert!(src.get_const(&dep).is_some(), "with_prelude lacks {dep}");
            let dep_unit = unit_of(src, &dep);
            if !visited.contains(&dep_unit) {
                stack.push((dep_unit, false));
            }
        }
    }
    order
}

pub(crate) fn copy_closure(src: &Environment, dst: &mut dyn Sink, roots: &[&str]) {
    for unit in closure_order(src, roots) {
        let (name, result) = match unit {
            Unit::Block(head) if dst.env().get_const(&head).is_none() => {
                let decl = block_decl(src, &head).0;
                (head, dst.add_ind(decl))
            }
            Unit::Decl(name) if dst.env().get_const(&name).is_none() => {
                let info = src.get_const(&name).expect("closure member");
                let (level_params, type_) = (info.level_params.clone(), info.type_.clone());
                let decl = match (info.kind, info.value.clone()) {
                    (ConstantKind::Definition, Some(value)) => Declaration::Definition {
                        name: name.clone(),
                        level_params,
                        type_,
                        value,
                        is_reducible: info.is_reducible,
                    },
                    (ConstantKind::Theorem, Some(value)) => Declaration::Theorem {
                        name: name.clone(),
                        level_params,
                        type_,
                        value,
                    },
                    (kind, _) => panic!("{name}: unexpected {kind:?} in the closure"),
                };
                (name, dst.add(decl))
            }
            _ => continue,
        };
        result.unwrap_or_else(|e| panic!("copying {name} was refused: {e}"));
    }
}

/// A transcription of `reconstruction()` in `src/tc/reduction/nat_parity.rs`
/// (private there; transcribed as of 2026-11-18, identical to probe v2's): the
/// goal `∀ n, Nat.div2Par n = n - (div2 n + div2 n)` and the proof term the
/// shortcut certifies before it decides `Nat.div2Par` natively.
pub(crate) fn reconstruction() -> (Expr, Expr) {
    let one = || vec![Level::succ(Level::zero())];
    let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let nat = || c("Nat");
    let app = |f: &str, args: Vec<Expr>| Expr::apps(c(f), args);
    let eq =
        |a: Expr, b: Expr| Expr::apps(Expr::const_(Name::from_string("Eq"), one()), [nat(), a, b]);
    let trans = |a: Expr, b: Expr, z: Expr, h: Expr, k: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), one()),
            [nat(), a, b, z, h, k],
        )
    };
    let n = Expr::bvar(0);
    let half = app("Nat.div2", vec![n.clone()]);
    let parity = app("Nat.div2Par", vec![n.clone()]);
    let doubled = app("Nat.add", vec![half.clone(), half]);
    let joined = app("Nat.add", vec![doubled.clone(), parity.clone()]);
    let commuted = app("Nat.add", vec![parity.clone(), doubled.clone()]);
    let h = trans(
        n.clone(),
        joined,
        commuted.clone(),
        app("Nat.div2_rejoin", vec![n.clone()]),
        app("Nat.add_comm", vec![doubled.clone(), parity.clone()]),
    );
    let rhs = app("Nat.sub", vec![n.clone(), doubled.clone()]);
    let middle = app("Nat.sub", vec![commuted.clone(), doubled.clone()]);
    let function = Expr::lam(
        BinderInfo::Default,
        nat(),
        app("Nat.sub", vec![Expr::bvar(0), doubled.lift(1)]),
    );
    let congr = Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()); 2],
        ),
        [nat(), nat(), n, commuted, function, h],
    );
    let subtract = app("Nat.add_sub_cancel", vec![parity.clone(), doubled]);
    let equality = trans(rhs.clone(), middle, parity.clone(), congr, subtract);
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), one()),
        [nat(), rhs.clone(), parity.clone(), equality],
    );
    (
        Expr::pi(BinderInfo::Default, nat(), eq(parity, rhs)),
        Expr::lam(BinderInfo::Default, nat(), proof),
    )
}
