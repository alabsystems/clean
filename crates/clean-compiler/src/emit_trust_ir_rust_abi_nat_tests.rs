// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C3: `Nat` through the pinned `trust_bignum::Nat` handle.
//!
//! trust-ir's reference interpreter cannot execute a call to a bodyless
//! declaration, so these tests run the emitted module on a small host
//! interpreter whose five pinned entry points are a model HEAP: `from_u64`,
//! `add` and `sub` allocate, `is_zero` reads, `drop` frees. Every read and
//! free checks the handle is live, and at the end of a top-level call the
//! only live handle may be the returned one — so a run proves the values
//! AND the ownership discipline (no leak, no double free, no use after free)
//! on that input. A mutation (one release removed) shows the check is not
//! vacuous.

use super::*;
use std::collections::{HashMap, HashSet};
use trust_ir::inst::{BinOp, CastOp, ICmpOp};
use trust_ir::Constant;

const NAT: &str = "def natAdd (a b : Nat) : Nat := a + b\n\
def natSub (a b : Nat) : Nat := a - b\n\
def natId (a : Nat) : Nat := a\n\
def natLit (a : Nat) : Nat := a + 5\n\
def natEq (a b : Nat) : Bool := a == b\n\
def natLe (a b : Nat) : Bool := decide (a ≤ b)\n\
def natLt (a b : Nat) : Bool := decide (a < b)\n\
def natSel (a b : Nat) : Nat := if a < b then a else b\n\
def isZ (a : Nat) : Bool := a == 0\n\
def toNatAdd (x : UInt64) (y : Nat) : Nat := x.toNat + y\n\
def tozero : Nat → Nat\n  | 0 => 0\n  | n+1 => tozero n\n";

const ROOTS: [&str; 11] = [
    "natAdd", "natSub", "natId", "natLit", "natEq", "natLe", "natLt", "natSel", "isZ", "toNatAdd",
    "tozero",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V {
    Int(u128),
    Bool(bool),
    Handle(u32),
}

#[derive(Default)]
struct Heap {
    cells: HashMap<u32, u128>,
    next: u32,
    allocated: u32,
}

impl Heap {
    fn alloc(&mut self, v: u128) -> V {
        self.next += 1;
        self.allocated += 1;
        self.cells.insert(self.next, v);
        V::Handle(self.next)
    }
    fn read(&self, h: V) -> Result<u128, String> {
        match h {
            V::Handle(id) => self
                .cells
                .get(&id)
                .copied()
                .ok_or_else(|| format!("use of released handle #{id}")),
            other => Err(format!("{other:?} is not a handle")),
        }
    }
}

fn width_mask(ty: &Ty) -> u128 {
    match ty {
        Ty::U8 => 0xff,
        Ty::U16 => 0xffff,
        Ty::U32 => 0xffff_ffff,
        Ty::U64 => u128::from(u64::MAX),
        _ => u128::MAX,
    }
}

/// Run `f` of `module` on `args`, with the pinned entry points as a model
/// heap.
fn exec(
    module: &Module,
    f: &trust_ir::Function,
    args: Vec<V>,
    heap: &mut Heap,
    depth: u32,
) -> Result<V, String> {
    if depth > 200 {
        return Err("recursion too deep".into());
    }
    let mut env: HashMap<ValueId, V> = HashMap::new();
    let mut block = f.entry;
    let mut incoming = args;
    loop {
        let b = f
            .blocks
            .iter()
            .find(|b| b.id == block)
            .ok_or_else(|| format!("no block {block:?}"))?;
        if b.params.len() != incoming.len() {
            return Err(format!("block {block:?} arity"));
        }
        for ((v, _), a) in b.params.iter().zip(incoming.drain(..)) {
            env.insert(*v, a);
        }
        let get = |env: &HashMap<ValueId, V>, v: &ValueId| {
            env.get(v).copied().ok_or_else(|| format!("unbound {v:?}"))
        };
        let mut next = None;
        for node in &b.body {
            let result = match &node.inst {
                Inst::Const { ty, value } => match value {
                    Constant::Int(i) => Some(V::Int((*i as u128) & width_mask(ty))),
                    Constant::Bool(x) => Some(V::Bool(*x)),
                    other => return Err(format!("constant {other:?}")),
                },
                Inst::BinOp { op, ty, lhs, rhs } => {
                    let (V::Int(a), V::Int(c)) = (get(&env, lhs)?, get(&env, rhs)?) else {
                        return Err("binop on non-int".into());
                    };
                    let r = match op {
                        BinOp::Add => a.wrapping_add(c),
                        BinOp::Sub => a.wrapping_sub(c),
                        BinOp::Mul => a.wrapping_mul(c),
                        BinOp::And => a & c,
                        BinOp::Or => a | c,
                        other => return Err(format!("binop {other:?}")),
                    };
                    Some(V::Int(r & width_mask(ty)))
                }
                Inst::ICmp { op, lhs, rhs, .. } => {
                    let (V::Int(a), V::Int(c)) = (get(&env, lhs)?, get(&env, rhs)?) else {
                        return Err("icmp on non-int".into());
                    };
                    Some(V::Bool(match op {
                        ICmpOp::Eq => a == c,
                        ICmpOp::Ult => a < c,
                        ICmpOp::Ule => a <= c,
                        other => return Err(format!("icmp {other:?}")),
                    }))
                }
                Inst::Select {
                    cond,
                    then_val,
                    else_val,
                    ..
                } => match get(&env, cond)? {
                    V::Bool(true) => Some(get(&env, then_val)?),
                    V::Bool(false) => Some(get(&env, else_val)?),
                    _ => return Err("select on non-bool".into()),
                },
                Inst::Cast {
                    op: CastOp::ZExt,
                    operand,
                    ..
                } => Some(get(&env, operand)?),
                Inst::Call { callee, args } => {
                    let g = module
                        .functions
                        .iter()
                        .find(|g| g.id == *callee)
                        .ok_or("no callee")?;
                    let vals = args
                        .iter()
                        .map(|a| get(&env, a))
                        .collect::<Result<Vec<_>, _>>()?;
                    if !g.blocks.is_empty() {
                        Some(exec(module, g, vals, heap, depth + 1)?)
                    } else {
                        match (g.name.as_str(), vals.as_slice()) {
                            ("trust_bignum_nat_from_u64", [V::Int(x)]) => Some(heap.alloc(*x)),
                            ("trust_bignum_nat_add", [a, c]) => {
                                let s = heap.read(*a)? + heap.read(*c)?;
                                Some(heap.alloc(s))
                            }
                            ("trust_bignum_nat_sub", [a, c]) => {
                                let s = heap.read(*a)?.saturating_sub(heap.read(*c)?);
                                Some(heap.alloc(s))
                            }
                            ("trust_bignum_nat_is_zero", [a]) => Some(V::Bool(heap.read(*a)? == 0)),
                            ("trust_bignum_nat_drop", [V::Handle(id)]) => {
                                if heap.cells.remove(id).is_none() {
                                    return Err(format!("double release of handle #{id}"));
                                }
                                None
                            }
                            (name, _) => return Err(format!("call to `{name}`")),
                        }
                    }
                }
                Inst::Br { target, args } => {
                    next = Some((
                        *target,
                        args.iter()
                            .map(|a| get(&env, a))
                            .collect::<Result<_, _>>()?,
                    ));
                    None
                }
                Inst::CondBr {
                    cond,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => {
                    let (t, a) = match get(&env, cond)? {
                        V::Bool(true) => (then_target, then_args),
                        V::Bool(false) => (else_target, else_args),
                        _ => return Err("condbr on non-bool".into()),
                    };
                    next = Some((
                        *t,
                        a.iter().map(|x| get(&env, x)).collect::<Result<_, _>>()?,
                    ));
                    None
                }
                Inst::Return { values } => {
                    let [v] = values.as_slice() else {
                        return Err("arity".into());
                    };
                    return get(&env, v);
                }
                other => return Err(format!("instruction {other:?}")),
            };
            if let (Some(r), Some(slot)) = (result, node.results.first()) {
                env.insert(*slot, r);
            }
            if next.is_some() {
                break;
            }
        }
        let (target, args) = next.ok_or("block without terminator")?;
        block = target;
        incoming = args;
    }
}

/// Call `name` as Rust would: the arguments are the caller's handles, freed
/// by the caller afterwards; the result is the caller's. Returns the result
/// as a number (handles read) and checks the heap is exactly that result.
fn call(module: &Module, name: &str, args: &[(bool, u128)]) -> Result<V, String> {
    let mut heap = Heap::default();
    let vals: Vec<V> = args
        .iter()
        .map(|(is_nat, v)| if *is_nat { heap.alloc(*v) } else { V::Int(*v) })
        .collect();
    let caller_owned: HashSet<u32> = heap.cells.keys().copied().collect();
    let r = exec(module, function(module, name), vals, &mut heap, 0)?;
    for id in &caller_owned {
        if !heap.cells.contains_key(id) {
            return Err(format!("the callee released its borrowed argument #{id}"));
        }
        heap.cells.remove(id);
    }
    let out = match r {
        V::Handle(id) => {
            let v = heap.read(r)?;
            heap.cells.remove(&id);
            V::Int(v)
        }
        other => other,
    };
    if !heap.cells.is_empty() {
        return Err(format!("leaked {} handle(s)", heap.cells.len()));
    }
    Ok(out)
}

fn nat(v: u128) -> (bool, u128) {
    (true, v)
}

#[test]
fn c3_nat_is_the_pinned_handle_and_needs_only_exported_entry_points() {
    let env = island_env(&[], NAT);
    for (level, pipeline) in levels() {
        let out = rust_abi(&env, &ROOTS, &[], &pipeline).unwrap_or_else(|e| panic!("{level}: {e}"));
        eprintln!("===== Nat {level} — Rust ABI =====\n{}", out.module);
        assert!(out.handle_bearing);
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        let add = function(&out.module, "natAdd");
        let ty = out.module.func_type(add.ty).expect("signature");
        assert_eq!(
            (ty.params.clone(), ty.returns.clone()),
            (vec![handle.clone(), handle.clone()], vec![handle])
        );
        assert_eq!(
            called(&out.module, add),
            vec!["trust_bignum_nat_add".to_string()],
            "{level}"
        );
        // Every bodyless declaration is one of the five exported shims.
        for f in out.module.functions.iter().filter(|f| f.is_declaration()) {
            assert!(
                carrier::NAT_ROLES
                    .iter()
                    .any(|r| f.name == format!("trust_bignum_nat_{r}")),
                "{level}: `{}` is not an exported pinned entry point",
                f.name
            );
            assert_eq!(
                f.calling_conv,
                trust_ir::CallingConv::C,
                "{level}: the pinned C shims"
            );
        }
    }
}

#[test]
fn c3_nat_values_and_ownership_on_edge_inputs() {
    let env = island_env(&[], NAT);
    let big = u128::from(u64::MAX);
    let edges = [0u128, 1, 2, 5, big - 1, big];
    for (level, pipeline) in levels() {
        let out = rust_abi(&env, &ROOTS, &[], &pipeline).unwrap_or_else(|e| panic!("{level}: {e}"));
        let m = &out.module;
        let run = |name: &str, args: &[(bool, u128)]| {
            call(m, name, args).unwrap_or_else(|e| panic!("{level}: {name}{args:?}: {e}"))
        };
        for &a in &edges {
            assert_eq!(run("natId", &[nat(a)]), V::Int(a), "{level}");
            assert_eq!(run("natLit", &[nat(a)]), V::Int(a + 5), "{level}");
            assert_eq!(run("isZ", &[nat(a)]), V::Bool(a == 0), "{level}");
            assert_eq!(
                run("toNatAdd", &[(false, a & big), nat(a)]),
                V::Int((a & big) + a),
                "{level}"
            );
            for &b in &edges {
                assert_eq!(run("natAdd", &[nat(a), nat(b)]), V::Int(a + b), "{level}");
                assert_eq!(
                    run("natSub", &[nat(a), nat(b)]),
                    V::Int(a.saturating_sub(b)),
                    "{level}"
                );
                assert_eq!(run("natEq", &[nat(a), nat(b)]), V::Bool(a == b), "{level}");
                assert_eq!(run("natLe", &[nat(a), nat(b)]), V::Bool(a <= b), "{level}");
                assert_eq!(run("natLt", &[nat(a), nat(b)]), V::Bool(a < b), "{level}");
                assert_eq!(
                    run("natSel", &[nat(a), nat(b)]),
                    V::Int(a.min(b)),
                    "{level}"
                );
            }
        }
        // `natAdd` past `u64::MAX`: the handle is unbounded.
        assert_eq!(
            run("natAdd", &[nat(big), nat(big)]),
            V::Int(2 * big),
            "{level}"
        );
        for n in [0u128, 1, 7, 40] {
            assert_eq!(run("tozero", &[nat(n)]), V::Int(0), "{level}: tozero({n})");
        }
    }
}

/// The ownership check is not vacuous: removing one release from the
/// emitted recursion makes the same run report the leak.
#[test]
fn c3_a_missing_release_is_caught() {
    let env = island_env(&[], NAT);
    let mut out = rust_abi(&env, &["tozero"], &[], &PipelineConfig::default()).expect("compiles");
    let drop_id = out
        .module
        .functions
        .iter()
        .find(|f| f.name == "trust_bignum_nat_drop")
        .map(|f| f.id)
        .expect("tozero releases something");
    let mut removed = false;
    for f in out
        .module
        .functions
        .iter_mut()
        .filter(|f| !f.blocks.is_empty())
    {
        for b in &mut f.blocks {
            if let Some(i) = b
                .body
                .iter()
                .position(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == drop_id))
            {
                if !removed {
                    b.body.remove(i);
                    removed = true;
                }
            }
        }
    }
    assert!(removed);
    let err = (1..5)
        .find_map(|n| call(&out.module, "tozero", &[nat(n)]).err())
        .expect("a removed release must leak on some input");
    assert!(err.contains("leaked"), "{err}");
}

/// Operations no exported entry point implements are refused by name, never
/// declared (a pinned symbol nothing links).
#[test]
fn c3_nat_operations_without_an_exported_shim_are_refused() {
    let env = island_env(&[], "def natMul (a b : Nat) : Nat := a * b\n");
    let err = rust_abi(&env, &["natMul"], &[], &PipelineConfig::default())
        .expect_err("Nat.mul has no exported shim");
    let text = err.to_string();
    assert!(
        text.contains("`natMul`") && text.contains("Nat.mul"),
        "{text}"
    );
}
