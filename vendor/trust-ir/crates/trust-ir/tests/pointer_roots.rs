// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `analysis::pointer_roots` (Trust design 2026-10-02, "C1", §3.3 and T-ir1):
//! the root each rule gives; parity with the census's private copy it
//! replaces, on representative and random functions; full roots, their sets
//! included, against an oracle written apart; every place that copy was
//! optimistic, where these roots are `Indirect`; how malformed shapes read;
//! and the escape bit against mem2reg's own promotion decision. Tests, not
//! proofs.

use std::collections::BTreeSet;

use trust_ir::analysis::{PointerRoot, PointerRoots, pointer_roots};
use trust_ir::constant::Constant;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{
    AllocOrigin, AssertKind, AtomicRMWOp, CastOp, Ordering, OverflowOp, PanicLocation, PanicSite,
    SwitchCase,
};
use trust_ir::mem2reg::promote_allocas_function;
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, CallingConv, FuncId, FuncTyId, Function, Inst, InstrNode, Ty, ValueId,
};

/// The census's private copy (Trust `fc0b6172f1`,
/// `crates/trust-thir-lower/src/effect_conservation.rs:389-398` and
/// `:988-1102`), verbatim but for its imports: what [`pointer_roots`]
/// projects onto.
mod census {
    use std::collections::{BTreeSet, HashMap};
    use trust_ir::{BlockId, Function, Inst, ValueId};

    /// Where a trust-ir store's pointer comes from.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum IrRoot {
        Arg(u32),
        Global,
        Indirect,
        /// The body's own `Alloca` / fresh `HeapAlloc`: not an effect.
        Local,
    }

    /// The incoming arguments of every block parameter, from every branch in `f`.
    fn ir_block_arg_sources(f: &Function) -> HashMap<ValueId, Vec<ValueId>> {
        let params: HashMap<BlockId, Vec<ValueId>> = f
            .blocks
            .iter()
            .map(|b| (b.id, b.params.iter().map(|(v, _)| *v).collect()))
            .collect();
        let mut out: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
        let mut bind = |target: &BlockId, args: &[ValueId]| {
            if let Some(ps) = params.get(target) {
                for (p, a) in ps.iter().zip(args) {
                    out.entry(*p).or_default().push(*a);
                }
            }
        };
        for node in f.blocks.iter().flat_map(|b| b.body.iter()) {
            match &node.inst {
                Inst::Br { target, args } => bind(target, args),
                Inst::CondBr {
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                    ..
                } => {
                    bind(then_target, then_args);
                    bind(else_target, else_args);
                }
                Inst::Switch {
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    bind(default, default_args);
                    for c in cases {
                        bind(&c.target, &c.args);
                    }
                }
                Inst::Invoke {
                    normal_dest,
                    normal_args,
                    ..
                } => bind(normal_dest, normal_args),
                _ => {}
            }
        }
        out
    }

    /// The pointer ROOT of every value of `f` (see [`IrRoot`]), by a monotone fixpoint over a flat
    /// lattice: unknown < {Arg(i), Global, Local, Indirect}; two different roots join to Indirect.
    pub fn ir_roots(f: &Function) -> HashMap<ValueId, IrRoot> {
        fn join(a: Option<IrRoot>, b: IrRoot) -> IrRoot {
            match a {
                None => b,
                Some(x) if x == b => x,
                Some(_) => IrRoot::Indirect,
            }
        }
        let mut roots: HashMap<ValueId, IrRoot> = HashMap::new();
        if let Some(entry) = f.blocks.iter().find(|b| b.id == f.entry) {
            for (i, (v, _)) in entry.params.iter().enumerate() {
                roots.insert(*v, IrRoot::Arg(i as u32));
            }
        }
        let incoming = ir_block_arg_sources(f);
        let entry_params: BTreeSet<ValueId> = f
            .blocks
            .iter()
            .find(|b| b.id == f.entry)
            .map(|b| b.params.iter().map(|(v, _)| *v).collect())
            .unwrap_or_default();
        // Bounded: every value can change at most twice (unknown -> root -> Indirect).
        for _ in 0..(2 * f
            .blocks
            .iter()
            .map(|b| b.body.len() + b.params.len())
            .sum::<usize>()
            + 2)
        {
            let mut changed = false;
            let mut set = |roots: &mut HashMap<ValueId, IrRoot>, v: ValueId, r: IrRoot| {
                let new = join(roots.get(&v).copied(), r);
                if roots.get(&v) != Some(&new) {
                    roots.insert(v, new);
                    changed = true;
                }
            };
            for b in &f.blocks {
                for (p, _) in &b.params {
                    if entry_params.contains(p) {
                        continue;
                    }
                    for src in incoming.get(p).map(Vec::as_slice).unwrap_or(&[]) {
                        if let Some(r) = roots.get(src).copied() {
                            set(&mut roots, *p, r);
                        }
                    }
                }
                for node in &b.body {
                    let Some(&res) = node.results.first() else {
                        continue;
                    };
                    let from =
                        |v: &ValueId, roots: &HashMap<ValueId, IrRoot>| roots.get(v).copied();
                    let r = match &node.inst {
                        Inst::GEP { base, .. } => from(base, &roots),
                        Inst::Copy { operand, .. } | Inst::Cast { operand, .. } => {
                            from(operand, &roots)
                        }
                        Inst::Borrow { ptr }
                        | Inst::BorrowMut { ptr }
                        | Inst::PtrData { ptr, .. } => from(ptr, &roots),
                        Inst::PtrFromParts { data, .. } => from(data, &roots),
                        Inst::ExtractField { aggregate, .. } => match from(aggregate, &roots) {
                            Some(IrRoot::Arg(i)) => Some(IrRoot::Arg(i)),
                            Some(_) => Some(IrRoot::Indirect),
                            None => None,
                        },
                        Inst::Select {
                            then_val, else_val, ..
                        } => match (from(then_val, &roots), from(else_val, &roots)) {
                            (Some(a), Some(b)) => Some(join(Some(a), b)),
                            (Some(a), None) | (None, Some(a)) => Some(a),
                            (None, None) => None,
                        },
                        Inst::GlobalAddr { .. } => Some(IrRoot::Global),
                        Inst::Alloca { .. } | Inst::HeapAlloc { .. } => Some(IrRoot::Local),
                        _ => Some(IrRoot::Indirect),
                    };
                    if let Some(r) = r {
                        set(&mut roots, res, r);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        roots
    }
}

/// The oracle for full roots, written apart from the analysis: the census's
/// round-robin fixpoint (every definition re-evaluated in each sweep until a
/// sweep changes nothing), set-valued, with its own join, and with every place
/// the census was optimistic corrected. Every edge [`Inst::successor_edges`]
/// lists binds, into every block that carries its target id, the entry
/// included; an edge whose argument count is not its target's parameter count
/// makes those parameters `Indirect`; an instruction's later results are
/// `Indirect`, and so is an operand nothing defines. A stale set in the
/// analysis (a change it did not propagate) shows as a difference here.
mod oracle {
    use std::collections::{BTreeSet, HashMap};
    use trust_ir::analysis::PointerRoot;
    use trust_ir::{Function, Inst, ValueId};

    fn join(old: Option<&PointerRoot>, new: &PointerRoot) -> PointerRoot {
        match (old, new) {
            (None, new) => new.clone(),
            (Some(PointerRoot::Arg(a)), PointerRoot::Arg(b)) if a == b => PointerRoot::Arg(*a),
            (Some(PointerRoot::Global(a)), PointerRoot::Global(b)) => PointerRoot::Global(a | b),
            (Some(PointerRoot::Local(a)), PointerRoot::Local(b)) => PointerRoot::Local(a | b),
            (Some(_), _) => PointerRoot::Indirect,
        }
    }

    pub fn roots(f: &Function) -> HashMap<ValueId, PointerRoot> {
        let mut defined: BTreeSet<ValueId> = BTreeSet::new();
        for b in &f.blocks {
            defined.extend(b.params.iter().map(|(v, _)| *v));
            for node in &b.body {
                defined.extend(node.results.iter().copied());
            }
        }
        let mut roots: HashMap<ValueId, PointerRoot> = HashMap::new();
        for entry in f.blocks.iter().filter(|b| b.id == f.entry) {
            for (i, (v, _)) in entry.params.iter().enumerate() {
                let root = join(roots.get(v), &PointerRoot::Arg(i as u32));
                roots.insert(*v, root);
            }
        }
        let mut incoming: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
        for node in f.blocks.iter().flat_map(|b| b.body.iter()) {
            for edge in node.inst.successor_edges() {
                for target in f.blocks.iter().filter(|b| b.id == edge.target) {
                    if target.params.len() == edge.args.len() {
                        for ((p, _), a) in target.params.iter().zip(edge.args) {
                            incoming.entry(*p).or_default().push(*a);
                        }
                    } else {
                        for (p, _) in &target.params {
                            roots.insert(*p, PointerRoot::Indirect);
                        }
                    }
                }
            }
        }
        loop {
            let mut changed = false;
            let mut set =
                |roots: &mut HashMap<ValueId, PointerRoot>, v: ValueId, r: PointerRoot| {
                    let new = join(roots.get(&v), &r);
                    if roots.get(&v) != Some(&new) {
                        roots.insert(v, new);
                        changed = true;
                    }
                };
            let from = |v: &ValueId, roots: &HashMap<ValueId, PointerRoot>| {
                roots
                    .get(v)
                    .cloned()
                    .or_else(|| (!defined.contains(v)).then_some(PointerRoot::Indirect))
            };
            for b in &f.blocks {
                for (p, _) in &b.params {
                    for src in incoming.get(p).map(Vec::as_slice).unwrap_or(&[]) {
                        if let Some(r) = from(src, &roots) {
                            set(&mut roots, *p, r);
                        }
                    }
                }
                for node in &b.body {
                    let Some((&res, later)) = node.results.split_first() else {
                        continue;
                    };
                    for v in later {
                        set(&mut roots, *v, PointerRoot::Indirect);
                    }
                    let r = match &node.inst {
                        Inst::GEP { base, .. } => from(base, &roots),
                        Inst::Copy { operand, .. } | Inst::Cast { operand, .. } => {
                            from(operand, &roots)
                        }
                        Inst::Borrow { ptr }
                        | Inst::BorrowMut { ptr }
                        | Inst::PtrData { ptr, .. } => from(ptr, &roots),
                        Inst::PtrFromParts { data, .. } => from(data, &roots),
                        Inst::ExtractField { aggregate, .. } => match from(aggregate, &roots) {
                            Some(PointerRoot::Arg(i)) => Some(PointerRoot::Arg(i)),
                            Some(_) => Some(PointerRoot::Indirect),
                            None => None,
                        },
                        Inst::Select {
                            then_val, else_val, ..
                        } => match (from(then_val, &roots), from(else_val, &roots)) {
                            (Some(a), Some(b)) => Some(join(Some(&a), &b)),
                            (Some(a), None) | (None, Some(a)) => Some(a),
                            (None, None) => None,
                        },
                        Inst::GlobalAddr { global } => {
                            Some(PointerRoot::Global(BTreeSet::from([*global])))
                        }
                        Inst::Alloca { .. } | Inst::HeapAlloc { .. } => {
                            Some(PointerRoot::Local(BTreeSet::from([res])))
                        }
                        _ => Some(PointerRoot::Indirect),
                    };
                    if let Some(r) = r {
                        set(&mut roots, res, r);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        roots
    }
}

use census::IrRoot;

// ---------------------------------------------------------------------------
// Builders
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn b(n: u32) -> BlockId {
    BlockId::new(n)
}
fn g(n: u32) -> GlobalId {
    GlobalId::new(n)
}
fn vs(ns: &[u32]) -> Vec<ValueId> {
    ns.iter().map(|n| v(*n)).collect()
}

fn at(result: u32, inst: Inst) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}
fn op(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn block(id: u32, params: &[u32], body: Vec<InstrNode>) -> Block {
    let mut block = Block::new(b(id));
    block.params = params.iter().map(|p| (v(*p), Ty::Ptr)).collect();
    block.body = body;
    block
}

/// A function whose entry is its first block.
fn function(blocks: Vec<Block>) -> Function {
    let mut function = Function::new(FuncId::new(0), "f", FuncTyId::new(0), blocks[0].id);
    function.blocks = blocks;
    function
}

fn alloca(r: u32) -> InstrNode {
    at(
        r,
        Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        },
    )
}
fn heap(r: u32) -> InstrNode {
    at(
        r,
        Inst::HeapAlloc {
            ty: Ty::I64,
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        },
    )
}
fn global(r: u32, id: u32) -> InstrNode {
    at(r, Inst::GlobalAddr { global: g(id) })
}
fn gep(r: u32, base: u32) -> InstrNode {
    at(
        r,
        Inst::GEP {
            pointee_ty: Ty::I64,
            base: v(base),
            indices: vec![],
            inbounds: true,
        },
    )
}
fn copy(r: u32, x: u32) -> InstrNode {
    at(
        r,
        Inst::Copy {
            ty: Ty::Ptr,
            operand: v(x),
        },
    )
}
fn cast(r: u32, cast_op: CastOp, x: u32) -> InstrNode {
    at(
        r,
        Inst::Cast {
            op: cast_op,
            src_ty: Ty::Ptr,
            dst_ty: Ty::Ptr,
            operand: v(x),
        },
    )
}
fn field(r: u32, aggregate: u32) -> InstrNode {
    at(
        r,
        Inst::ExtractField {
            ty: Ty::Ptr,
            aggregate: v(aggregate),
            field: 0,
        },
    )
}
fn select(r: u32, then_val: u32, else_val: u32) -> InstrNode {
    at(
        r,
        Inst::Select {
            ty: Ty::Ptr,
            cond: v(999),
            then_val: v(then_val),
            else_val: v(else_val),
        },
    )
}
fn load(r: u32, ptr: u32) -> InstrNode {
    at(
        r,
        Inst::Load {
            ty: Ty::I64,
            ptr: v(ptr),
            volatile: false,
            align: None,
        },
    )
}
fn store(ptr: u32, value: u32) -> InstrNode {
    op(Inst::Store {
        ty: Ty::I64,
        ptr: v(ptr),
        value: v(value),
        volatile: false,
        align: None,
    })
}
fn konst(r: u32) -> InstrNode {
    at(
        r,
        Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        },
    )
}
fn call(r: u32, args: &[u32]) -> InstrNode {
    at(
        r,
        Inst::Call {
            callee: FuncId::new(7),
            args: vs(args),
        },
    )
}
fn br(target: u32, args: &[u32]) -> InstrNode {
    op(Inst::Br {
        target: b(target),
        args: vs(args),
    })
}
fn cond_br(then_target: u32, then_args: &[u32], else_target: u32, else_args: &[u32]) -> InstrNode {
    op(Inst::CondBr {
        cond: v(999),
        then_target: b(then_target),
        then_args: vs(then_args),
        else_target: b(else_target),
        else_args: vs(else_args),
    })
}
fn switch(default: u32, default_args: &[u32], case: u32, case_args: &[u32]) -> InstrNode {
    op(Inst::Switch {
        value: v(999),
        default: b(default),
        default_args: vs(default_args),
        cases: vec![SwitchCase {
            value: Constant::Int(0),
            target: b(case),
            args: vs(case_args),
        }],
        exhaustive_enum_unreachable: false,
    })
}
fn invoke(r: u32, normal: u32, normal_args: &[u32], unwind: u32) -> InstrNode {
    at(
        r,
        Inst::Invoke {
            callee: FuncId::new(7),
            args: vec![],
            normal_dest: b(normal),
            normal_args: vs(normal_args),
            unwind_dest: b(unwind),
        },
    )
}
fn assert_invoke(normal: u32, normal_args: &[u32], unwind: u32) -> InstrNode {
    op(Inst::AssertInvoke {
        cond: v(999),
        kind: AssertKind::Unspecified,
        site: PanicSite {
            entry: FuncId::new(8),
            location: PanicLocation::Global(g(9)),
        },
        normal_dest: b(normal),
        normal_args: vs(normal_args),
        unwind_dest: b(unwind),
    })
}
fn drop_invoke(ptr: u32, normal: u32, normal_args: &[u32], unwind: u32) -> InstrNode {
    op(Inst::DropInvoke {
        ty: Ty::I64,
        ptr: v(ptr),
        normal_dest: b(normal),
        normal_args: vs(normal_args),
        unwind_dest: b(unwind),
    })
}
fn invoke_indirect(
    r: u32,
    callee: u32,
    normal: u32,
    normal_args: &[u32],
    unwind: u32,
) -> InstrNode {
    at(
        r,
        Inst::InvokeIndirect {
            callee: v(callee),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::Rust,
            normal_dest: b(normal),
            normal_args: vs(normal_args),
            unwind_dest: b(unwind),
        },
    )
}
fn ret(values: &[u32]) -> InstrNode {
    op(Inst::Return { values: vs(values) })
}

fn arg(i: u32) -> PointerRoot {
    PointerRoot::Arg(i)
}
fn globals(ids: &[u32]) -> PointerRoot {
    PointerRoot::Global(ids.iter().map(|id| g(*id)).collect())
}
fn locals(sites: &[u32]) -> PointerRoot {
    PointerRoot::Local(sites.iter().map(|site| v(*site)).collect())
}

/// Every value `function` defines or uses.
fn mentioned(function: &Function) -> BTreeSet<ValueId> {
    let mut values = BTreeSet::new();
    for block in &function.blocks {
        values.extend(block.params.iter().map(|(value, _)| *value));
        for node in &block.body {
            values.extend(node.results.iter().copied());
            node.inst.visit_value_operands(|value| {
                values.insert(value);
            });
        }
    }
    values
}

fn project(root: &PointerRoot) -> IrRoot {
    match root {
        PointerRoot::Arg(index) => IrRoot::Arg(*index),
        PointerRoot::Global(_) => IrRoot::Global,
        PointerRoot::Local(_) => IrRoot::Local,
        PointerRoot::Indirect => IrRoot::Indirect,
    }
}

/// Each value's root as the census reads it (`unwrap_or(Indirect)`), against
/// this analysis's projected root.
fn against_census(function: &Function) -> Vec<(ValueId, IrRoot, IrRoot)> {
    let old = census::ir_roots(function);
    let new = pointer_roots(function);
    mentioned(function)
        .into_iter()
        .map(|value| {
            (
                value,
                old.get(&value).copied().unwrap_or(IrRoot::Indirect),
                project(new.root(value)),
            )
        })
        .collect()
}

/// The projection is the census's root of every value, and the full root
/// (sets included) is the oracle's.
fn assert_parity(function: &Function) {
    for (value, old, new) in against_census(function) {
        assert_eq!(new, old, "{value:?} in {function:#?}");
    }
    assert_complete_parity(function);
}

/// The full root of every value, its sets included, is the oracle's.
fn assert_complete_parity(function: &Function) {
    let expected = oracle::roots(function);
    let roots = pointer_roots(function);
    for value in mentioned(function) {
        assert_eq!(
            roots.root(value),
            expected.get(&value).unwrap_or(&PointerRoot::Indirect),
            "{value:?} in {function:#?}"
        );
    }
}

/// A private pointer is the private allocation itself: anything derived from
/// an allocation is a use of it, so the allocation escapes.
fn assert_private_is_the_allocation(function: &Function, roots: &PointerRoots) {
    for value in mentioned(function) {
        if roots.is_private(value) {
            assert_eq!(roots.root(value), &locals(&[value.index()]), "{value:?}");
            assert_eq!(roots.escapes(value), Some(false));
        }
    }
}

// ---------------------------------------------------------------------------
// The rules
// ---------------------------------------------------------------------------

#[test]
fn each_definition_has_its_root() {
    let f = function(vec![block(
        0,
        &[0, 1],
        vec![
            gep(2, 0),
            copy(3, 2),
            cast(4, CastOp::PtrToInt, 3),
            cast(5, CastOp::IntToPtr, 4),
            at(6, Inst::Borrow { ptr: v(0) }),
            at(7, Inst::BorrowMut { ptr: v(1) }),
            at(
                8,
                Inst::PtrData {
                    ptr_ty: Ty::Ptr,
                    ptr: v(1),
                },
            ),
            at(
                9,
                Inst::PtrFromParts {
                    ptr_ty: Ty::Ptr,
                    metadata_ty: Ty::Usize,
                    data: v(0),
                    metadata: v(1),
                },
            ),
            field(10, 0),
            global(11, 0),
            gep(12, 11),
            global(13, 1),
            select(14, 11, 13),
            alloca(15),
            heap(16),
            select(17, 15, 16),
            field(18, 11),
            field(19, 15),
            load(20, 0),
            call(21, &[]),
            konst(22),
            at(23, Inst::NullPtr),
            select(24, 0, 1),
            select(25, 0, 11),
            select(26, 15, 11),
            select(27, 0, 0),
            ret(&[]),
        ],
    )]);
    let roots = pointer_roots(&f);
    let expect = [
        (0, arg(0)),
        (1, arg(1)),
        (2, arg(0)),
        (3, arg(0)),
        (4, arg(0)),
        (5, arg(0)),
        (6, arg(0)),
        (7, arg(1)),
        (8, arg(1)),
        (9, arg(0)),
        (10, arg(0)),
        (11, globals(&[0])),
        (12, globals(&[0])),
        (13, globals(&[1])),
        (14, globals(&[0, 1])),
        (15, locals(&[15])),
        (16, locals(&[16])),
        (17, locals(&[15, 16])),
        (18, PointerRoot::Indirect),
        (19, PointerRoot::Indirect),
        (20, PointerRoot::Indirect),
        (21, PointerRoot::Indirect),
        (22, PointerRoot::Indirect),
        (23, PointerRoot::Indirect),
        (24, PointerRoot::Indirect),
        (25, PointerRoot::Indirect),
        (26, PointerRoot::Indirect),
        (27, arg(0)),
        // Not defined anywhere (the select condition): any address.
        (999, PointerRoot::Indirect),
        // Not mentioned at all.
        (5000, PointerRoot::Indirect),
    ];
    for (value, root) in expect {
        assert_eq!(roots.root(v(value)), &root, "%{value}");
    }
    assert_parity(&f);
}

#[test]
fn the_join_is_the_least_upper_bound() {
    let all = [
        arg(0),
        arg(1),
        globals(&[0]),
        globals(&[1]),
        globals(&[0, 1]),
        locals(&[3]),
        locals(&[4]),
        locals(&[3, 4]),
        PointerRoot::Indirect,
    ];
    let below = |x: &PointerRoot, y: &PointerRoot| x.join(y) == *y;
    for x in &all {
        assert_eq!(x.join(x), *x, "idempotent");
        assert_eq!(x.join(&PointerRoot::Indirect), PointerRoot::Indirect);
        for y in &all {
            let joined = x.join(y);
            assert_eq!(joined, y.join(x), "commutative");
            assert!(below(x, &joined) && below(y, &joined), "an upper bound");
            for z in &all {
                assert_eq!(x.join(y).join(z), x.join(&y.join(z)), "associative");
                if below(x, z) && below(y, z) {
                    assert!(below(&joined, z), "the least one");
                }
            }
        }
    }
    assert_eq!(arg(0).join(&arg(1)), PointerRoot::Indirect);
    assert_eq!(globals(&[0]).join(&locals(&[3])), PointerRoot::Indirect);
}

/// Every normal edge binds its arguments: `Br`, both `CondBr` arms, `Switch`
/// cases and default, `Invoke`; and a loop keeps the root its entry gives.
#[test]
fn block_parameters_join_every_incoming_edge() {
    let f = function(vec![
        block(
            0,
            &[0],
            vec![
                alloca(1),
                alloca(2),
                global(3, 0),
                cond_br(1, &[1], 2, &[2]),
            ],
        ),
        block(1, &[10], vec![br(3, &[10, 0, 3])]),
        block(2, &[11], vec![switch(3, &[11, 0, 3], 4, &[])]),
        block(3, &[12, 13, 14], vec![ret(&[])]),
        block(4, &[], vec![invoke(15, 5, &[3], 6)]),
        block(5, &[16], vec![br(7, &[0])]),
        block(6, &[], vec![ret(&[])]),
        // A loop: the header's parameter is the entry's argument, advanced.
        block(7, &[17], vec![gep(18, 17), cond_br(7, &[18], 8, &[])]),
        block(8, &[], vec![ret(&[])]),
        // No edge reaches this block: its parameter stays unset (Indirect).
        block(9, &[19], vec![copy(20, 19), select(21, 19, 1), ret(&[])]),
    ]);
    let roots = pointer_roots(&f);
    assert_eq!(roots.root(v(10)), &locals(&[1]));
    assert_eq!(roots.root(v(11)), &locals(&[2]));
    assert_eq!(roots.root(v(12)), &locals(&[1, 2]));
    assert_eq!(roots.root(v(13)), &arg(0));
    assert_eq!(roots.root(v(14)), &globals(&[0]));
    assert_eq!(roots.root(v(16)), &globals(&[0]));
    assert_eq!(roots.root(v(17)), &arg(0));
    assert_eq!(roots.root(v(18)), &arg(0));
    assert_eq!(roots.root(v(19)), &PointerRoot::Indirect);
    assert_eq!(roots.root(v(20)), &PointerRoot::Indirect);
    assert_eq!(roots.root(v(21)), &locals(&[1]), "as the census joins");
    assert_parity(&f);
}

// ---------------------------------------------------------------------------
// Parity with the census, and where the census was optimistic
// ---------------------------------------------------------------------------

/// The shapes the census's corpus stores through: a parameter, a field of a
/// by-value parameter, a global, its own locals, a loaded pointer, a call
/// result, and joins of them across a diamond and a loop.
#[test]
fn the_census_shapes_project_onto_the_census_roots() {
    let shapes = [
        // `*p = x`, `p.0 = x` through a GEP, `(*s).f = x` via a field.
        function(vec![block(
            0,
            &[0, 1],
            vec![
                gep(2, 0),
                store(2, 1),
                field(3, 1),
                gep(4, 3),
                store(4, 1),
                store(0, 1),
                ret(&[]),
            ],
        )]),
        // `static mut G` and a promoted local, joined across a diamond.
        function(vec![
            block(
                0,
                &[0],
                vec![global(1, 0), alloca(2), cond_br(1, &[1], 2, &[2])],
            ),
            block(1, &[3], vec![store(3, 0), br(3, &[3])]),
            block(2, &[4], vec![store(4, 0), br(3, &[4])]),
            block(3, &[5], vec![store(5, 0), ret(&[])]),
        ]),
        // A loaded pointer and a call result, carried round a loop.
        function(vec![
            block(0, &[0], vec![load(1, 0), call(2, &[0]), br(1, &[1, 0])]),
            block(
                1,
                &[3, 4],
                vec![store(3, 4), gep(5, 4), cond_br(1, &[2, 5], 2, &[])],
            ),
            block(2, &[], vec![ret(&[])]),
        ]),
        // An `Invoke` whose normal edge carries its own result and a local.
        function(vec![
            block(0, &[0], vec![alloca(1), invoke(2, 1, &[2, 1], 2)]),
            block(1, &[3, 4], vec![store(3, 0), store(4, 0), ret(&[])]),
            block(2, &[], vec![ret(&[])]),
        ]),
    ];
    for f in &shapes {
        assert_parity(f);
        assert_private_is_the_allocation(f, &pointer_roots(f));
    }
}

/// The census omitted three normal edges; a value they carry is `Indirect`
/// here where the census read the other edge's root alone.
#[test]
fn every_normal_edge_binds_its_arguments() {
    let join_block = |edge: InstrNode| {
        function(vec![
            block(0, &[0], vec![alloca(1), cond_br(1, &[1], 2, &[])]),
            block(1, &[10], vec![store(10, 0), ret(&[])]),
            block(2, &[], vec![edge]),
            block(3, &[], vec![ret(&[])]),
        ])
    };
    for edge in [
        assert_invoke(1, &[0], 3),
        drop_invoke(1, 1, &[0], 3),
        invoke_indirect(20, 0, 1, &[0], 3),
    ] {
        let f = join_block(edge);
        assert_eq!(pointer_roots(&f).root(v(10)), &PointerRoot::Indirect);
        assert_eq!(census::ir_roots(&f).get(&v(10)), Some(&IrRoot::Local));
        assert_complete_parity(&f);
    }
    // The `Invoke` the census did list agrees.
    let f = join_block(invoke(20, 1, &[0], 3));
    assert_eq!(pointer_roots(&f).root(v(10)), &PointerRoot::Indirect);
    assert_parity(&f);
}

/// A later result of an instruction is `Indirect`: joined with a local it
/// gives `Indirect`, where the census joined it as nothing.
#[test]
fn a_later_result_is_indirect() {
    let mut pair = call(1, &[]);
    pair.results = vs(&[1, 2]);
    let mut overflow = at(
        3,
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(0),
        },
    );
    overflow.results = vs(&[3, 4]);
    let f = function(vec![
        block(
            0,
            &[0],
            vec![pair, overflow, alloca(5), cond_br(1, &[2], 1, &[5])],
        ),
        block(1, &[6], vec![select(7, 4, 5), store(6, 0), ret(&[])]),
    ]);
    let roots = pointer_roots(&f);
    assert_eq!(roots.root(v(2)), &PointerRoot::Indirect);
    assert_eq!(roots.root(v(6)), &PointerRoot::Indirect);
    assert_eq!(roots.root(v(7)), &PointerRoot::Indirect);
    let old = census::ir_roots(&f);
    assert_eq!(old.get(&v(6)), Some(&IrRoot::Local));
    assert_eq!(old.get(&v(7)), Some(&IrRoot::Local));
    assert_complete_parity(&f);
}

/// An edge into the entry block joins into its parameters: the census kept
/// `Arg(i)` whatever the edge passed.
#[test]
fn an_edge_into_the_entry_joins_its_parameters() {
    let f = function(vec![
        block(0, &[0], vec![store(0, 0), br(1, &[])]),
        block(1, &[], vec![global(1, 0), br(0, &[1])]),
    ]);
    assert_eq!(pointer_roots(&f).root(v(0)), &PointerRoot::Indirect);
    assert_eq!(census::ir_roots(&f).get(&v(0)), Some(&IrRoot::Arg(0)));
    assert_complete_parity(&f);
    // The same edge passing the parameter itself keeps it.
    let f = function(vec![
        block(0, &[0], vec![store(0, 0), br(1, &[])]),
        block(1, &[], vec![br(0, &[0])]),
    ]);
    assert_eq!(pointer_roots(&f).root(v(0)), &arg(0));
}

/// An operand nothing defines may be any address: the census joined it as
/// nothing.
#[test]
fn an_undefined_operand_is_indirect() {
    let f = function(vec![block(
        0,
        &[],
        vec![
            alloca(1),
            select(2, 1, 77),
            gep(3, 78),
            store(2, 1),
            ret(&[]),
        ],
    )]);
    let roots = pointer_roots(&f);
    assert_eq!(roots.root(v(2)), &PointerRoot::Indirect);
    assert_eq!(roots.root(v(3)), &PointerRoot::Indirect);
    assert_eq!(census::ir_roots(&f).get(&v(2)), Some(&IrRoot::Local));
    assert_complete_parity(&f);
}

/// A set that grows on a second trip round a loop reaches everything derived
/// from it: the join is recomputed downstream whenever a set grows, not only
/// when the class changes.
#[test]
fn a_set_that_grows_round_a_loop_reaches_every_copy() {
    let f = function(vec![
        block(0, &[0], vec![global(1, 0), br(1, &[1])]),
        block(
            1,
            &[2],
            vec![
                copy(3, 2),
                copy(4, 3),
                copy(5, 4),
                global(6, 1),
                select(7, 5, 6),
                cond_br(1, &[7], 2, &[]),
            ],
        ),
        block(2, &[], vec![ret(&[])]),
    ]);
    let roots = pointer_roots(&f);
    for value in [2, 3, 4, 5, 7] {
        assert_eq!(roots.root(v(value)), &globals(&[0, 1]), "%{value}");
    }
    assert_parity(&f);
}

// ---------------------------------------------------------------------------
// Shapes the validator rejects: the roots read each at least as high as any
// resolution of it, and the census read some of them lower
// ---------------------------------------------------------------------------

/// An edge whose argument count is not its target's parameter count, an
/// unwind edge into a landing pad with parameters among them, makes each of
/// those parameters `Indirect`. The census bound a prefix, left the rest
/// unset and joined them as nothing.
#[test]
fn an_edge_with_the_wrong_argument_count_makes_its_targets_parameters_indirect() {
    // %1 is a local; the edge into block 1 passes one argument for two
    // parameters; block 2 joins %3 with the local.
    let short = function(vec![
        block(0, &[0], vec![alloca(1), cond_br(1, &[1], 2, &[1])]),
        block(1, &[2, 3], vec![br(2, &[3])]),
        block(2, &[4], vec![store(4, 0), ret(&[])]),
    ]);
    let roots = pointer_roots(&short);
    assert_eq!(roots.root(v(2)), &PointerRoot::Indirect);
    assert_eq!(roots.root(v(3)), &PointerRoot::Indirect);
    assert_eq!(roots.root(v(4)), &PointerRoot::Indirect);
    let old = census::ir_roots(&short);
    assert_eq!(old.get(&v(2)), Some(&IrRoot::Local));
    assert_eq!(old.get(&v(3)), None);
    assert_eq!(old.get(&v(4)), Some(&IrRoot::Local), "joined as nothing");
    assert_complete_parity(&short);

    // A landing pad with a parameter: its unwind edge passes none.
    let pad = function(vec![
        block(0, &[0], vec![alloca(1), invoke(2, 1, &[1], 2)]),
        block(1, &[3], vec![br(3, &[3])]),
        block(2, &[4], vec![br(3, &[4])]),
        block(3, &[5], vec![store(5, 0), ret(&[])]),
    ]);
    let roots = pointer_roots(&pad);
    assert_eq!(roots.root(v(4)), &PointerRoot::Indirect);
    assert_eq!(roots.root(v(5)), &PointerRoot::Indirect);
    let old = census::ir_roots(&pad);
    assert_eq!(old.get(&v(4)), None);
    assert_eq!(old.get(&v(5)), Some(&IrRoot::Local), "joined as nothing");
    assert_complete_parity(&pad);

    // One argument too many is no better.
    let long = function(vec![
        block(0, &[0], vec![alloca(1), br(1, &[1, 1])]),
        block(1, &[2], vec![store(2, 0), ret(&[])]),
    ]);
    assert_eq!(pointer_roots(&long).root(v(2)), &PointerRoot::Indirect);
    assert_eq!(census::ir_roots(&long).get(&v(2)), Some(&IrRoot::Local));
    assert_complete_parity(&long);
}

/// A repeated entry-parameter id joins its positions to `Indirect`; the
/// census kept `Arg` of the last one.
#[test]
fn a_repeated_entry_parameter_id_is_indirect() {
    let f = function(vec![block(0, &[0, 0], vec![store(0, 0), ret(&[])])]);
    assert_eq!(pointer_roots(&f).root(v(0)), &PointerRoot::Indirect);
    assert_eq!(census::ir_roots(&f).get(&v(0)), Some(&IrRoot::Arg(1)));
    assert_complete_parity(&f);
}

/// A block id two blocks carry binds an edge to both, and a repeated entry
/// id gives each such block's parameters `Arg(i)`. The census bound only the
/// last block carrying an id and gave `Arg(i)` only to the first entry: a
/// parameter of another such block read `Indirect` there, but was joined as
/// nothing into what it flowed to.
#[test]
fn a_repeated_block_id_binds_every_block_that_carries_it() {
    let f = function(vec![
        block(0, &[0], vec![alloca(1), br(1, &[1])]),
        block(1, &[2], vec![store(2, 0), br(2, &[2])]),
        block(1, &[3], vec![store(3, 0), ret(&[])]),
        block(2, &[4], vec![store(4, 0), ret(&[])]),
    ]);
    let roots = pointer_roots(&f);
    assert_eq!(roots.root(v(2)), &locals(&[1]));
    assert_eq!(roots.root(v(3)), &locals(&[1]));
    assert_eq!(roots.root(v(4)), &locals(&[1]));
    let old = census::ir_roots(&f);
    assert_eq!(old.get(&v(2)), None, "the shadowed block is not bound");
    assert_eq!(old.get(&v(3)), Some(&IrRoot::Local));
    assert_eq!(old.get(&v(4)), None);
    assert_complete_parity(&f);

    let f = function(vec![
        block(0, &[0], vec![store(0, 0), ret(&[])]),
        block(0, &[1], vec![store(1, 1), ret(&[])]),
    ]);
    let roots = pointer_roots(&f);
    assert_eq!(roots.root(v(0)), &arg(0));
    assert_eq!(roots.root(v(1)), &arg(0));
    let old = census::ir_roots(&f);
    assert_eq!(old.get(&v(0)), Some(&IrRoot::Arg(0)));
    assert_eq!(old.get(&v(1)), None);
    assert_complete_parity(&f);
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

/// A random function of pointer-shaped definitions over a random CFG. In the
/// census's shape (`wide == false`) its edges are `Br`, `CondBr`, `Switch`
/// and `Invoke`, none enters the entry, each passes as many arguments as its
/// target has parameters (an unwind edge enters a block with none), every
/// operand is defined and every instruction has at most one result. `wide`
/// adds the rest: the other invoke-family edges, edges into the entry, edges
/// with the wrong argument count (unwind edges into blocks with parameters
/// among them), two-result instructions and undefined operands.
fn random_function(rng: &mut Rng, wide: bool) -> Function {
    let count = 1 + rng.below(6);
    let mut next = 0u32;
    let mut fresh = || {
        next += 1;
        next - 1
    };
    let mut blocks: Vec<Block> = (0..count)
        .map(|id| {
            // The entry has a parameter, so every pick has a defined value.
            // In the census's shape the last block has none: it is the
            // landing pad every unwind edge enters.
            let arity = if !wide && id > 0 && id == count - 1 {
                0
            } else {
                rng.below(4) + usize::from(id == 0)
            };
            let params: Vec<u32> = (0..arity).map(|_| fresh()).collect();
            block(id as u32, &params, vec![])
        })
        .collect();
    let mut pool: Vec<u32> = blocks
        .iter()
        .flat_map(|block| block.params.iter().map(|(value, _)| value.index()))
        .collect();
    let pick = |rng: &mut Rng, pool: &[u32]| -> u32 {
        if wide && rng.chance(4) {
            10_000 + rng.below(4) as u32
        } else {
            pool[rng.below(pool.len())]
        }
    };
    let arities: Vec<usize> = blocks.iter().map(|block| block.params.len()).collect();
    for block in &mut blocks {
        let mut body = Vec::new();
        for _ in 0..rng.below(9) {
            let r = fresh();
            let node = match rng.below(if wide { 20 } else { 18 }) {
                0 => alloca(r),
                1 => heap(r),
                2 => global(r, rng.below(3) as u32),
                3 => gep(r, pick(rng, &pool)),
                4 => copy(r, pick(rng, &pool)),
                5 => cast(r, CastOp::PtrToPtr, pick(rng, &pool)),
                6 => at(
                    r,
                    Inst::Borrow {
                        ptr: v(pick(rng, &pool)),
                    },
                ),
                7 => at(
                    r,
                    Inst::BorrowMut {
                        ptr: v(pick(rng, &pool)),
                    },
                ),
                8 => at(
                    r,
                    Inst::PtrData {
                        ptr_ty: Ty::Ptr,
                        ptr: v(pick(rng, &pool)),
                    },
                ),
                9 => at(
                    r,
                    Inst::PtrFromParts {
                        ptr_ty: Ty::Ptr,
                        metadata_ty: Ty::Usize,
                        data: v(pick(rng, &pool)),
                        metadata: v(pick(rng, &pool)),
                    },
                ),
                10 => field(r, pick(rng, &pool)),
                11 | 12 => {
                    let (then_val, else_val) = (pick(rng, &pool), pick(rng, &pool));
                    select(r, then_val, else_val)
                }
                13 => load(r, pick(rng, &pool)),
                14 => call(r, &[pick(rng, &pool)]),
                15 => konst(r),
                16 => {
                    let (ptr, value) = (pick(rng, &pool), pick(rng, &pool));
                    store(ptr, value)
                }
                17 => at(r, Inst::NullPtr),
                _ => {
                    let mut pair = call(r, &[]);
                    pair.results.push(v(fresh()));
                    pair
                }
            };
            pool.extend(node.results.iter().map(|value| value.index()));
            body.push(node);
        }
        let target = |rng: &mut Rng| -> u32 {
            if wide || count == 1 {
                rng.below(count) as u32
            } else {
                1 + rng.below(count - 1) as u32
            }
        };
        // An unwind edge passes no arguments: in the census's shape it
        // enters a block with no parameters; the wide shape may break that.
        let landing_pad = |rng: &mut Rng| -> u32 {
            if wide {
                target(rng)
            } else {
                let pads: Vec<u32> = (1..count as u32)
                    .filter(|id| arities[*id as usize] == 0)
                    .collect();
                pads[rng.below(pads.len())]
            }
        };
        // The wide shape sometimes passes one argument too many or too few.
        let args = |rng: &mut Rng, pool: &[u32], target: u32| -> Vec<u32> {
            let arity = arities[target as usize];
            let arity = match (wide && rng.chance(5), rng.chance(50)) {
                (false, _) => arity,
                (true, true) => arity + 1,
                (true, false) => arity.saturating_sub(1),
            };
            (0..arity).map(|_| pick(rng, pool)).collect()
        };
        let can_branch = wide || count > 1;
        let terminator = match rng.below(if wide { 8 } else { 5 }) {
            _ if !can_branch => ret(&[]),
            0 => ret(&[]),
            1 => {
                let t = target(rng);
                br(t, &args(rng, &pool, t))
            }
            2 => {
                let (then_target, else_target) = (target(rng), target(rng));
                let then_args = args(rng, &pool, then_target);
                cond_br(
                    then_target,
                    &then_args,
                    else_target,
                    &args(rng, &pool, else_target),
                )
            }
            3 => {
                let (default, case) = (target(rng), target(rng));
                let default_args = args(rng, &pool, default);
                switch(default, &default_args, case, &args(rng, &pool, case))
            }
            4 => {
                let r = fresh();
                pool.push(r);
                let (normal, unwind) = (target(rng), landing_pad(rng));
                invoke(r, normal, &args(rng, &pool, normal), unwind)
            }
            5 => {
                let (normal, unwind) = (target(rng), landing_pad(rng));
                assert_invoke(normal, &args(rng, &pool, normal), unwind)
            }
            6 => {
                let (normal, unwind) = (target(rng), landing_pad(rng));
                drop_invoke(pick(rng, &pool), normal, &args(rng, &pool, normal), unwind)
            }
            _ => {
                let r = fresh();
                pool.push(r);
                let (normal, unwind) = (target(rng), landing_pad(rng));
                invoke_indirect(
                    r,
                    pick(rng, &pool),
                    normal,
                    &args(rng, &pool, normal),
                    unwind,
                )
            }
        };
        body.push(terminator);
        block.body = body;
    }
    function(blocks)
}

/// T-ir1 on random functions: in the census's shape the projection IS the
/// census's root of every value; in both shapes the full root, its sets
/// included, is the oracle's, so the corrections are the only difference.
#[test]
fn random_functions_project_onto_the_census_roots() {
    let mut rng = Rng(0xc1_9017_7e55);
    let mut seen: BTreeSet<IrRoot> = BTreeSet::new();
    let mut joined_sets = 0;
    let mut corrected = 0;
    let mut mismatched = 0;
    for _ in 0..1500 {
        let f = random_function(&mut rng, false);
        assert_parity(&f);
        let roots = pointer_roots(&f);
        assert_private_is_the_allocation(&f, &roots);
        for value in mentioned(&f) {
            let root = roots.root(value);
            seen.insert(project(root));
            joined_sets += usize::from(
                matches!(
                    root,
                    PointerRoot::Global(set) if set.len() > 1
                ) || matches!(root, PointerRoot::Local(set) if set.len() > 1),
            );
        }
        let f = random_function(&mut rng, true);
        assert_complete_parity(&f);
        assert_private_is_the_allocation(&f, &pointer_roots(&f));
        corrected += usize::from(against_census(&f).iter().any(|(_, old, new)| old != new));
        mismatched += usize::from(f.blocks.iter().flat_map(|b| &b.body).any(|node| {
            node.inst.successor_edges().iter().any(|edge| {
                f.blocks.iter().any(|target| {
                    target.id == edge.target && target.params.len() != edge.args.len()
                })
            })
        }));
    }
    // Not vacuous: every class occurs, and joins kept their sets.
    for class in [
        IrRoot::Arg(0),
        IrRoot::Global,
        IrRoot::Local,
        IrRoot::Indirect,
    ] {
        assert!(seen.contains(&class), "{class:?}: {seen:?}");
    }
    assert!(joined_sets > 50, "{joined_sets}");
    // ... and the wide shape exercised the corrections, and edges with the
    // wrong argument count.
    assert!(corrected > 100, "{corrected}");
    assert!(mismatched > 100, "{mismatched}");
}

// ---------------------------------------------------------------------------
// Escape
// ---------------------------------------------------------------------------

/// T-ir1's second half: on every use shape, the escape bit of a scalar alloca
/// is exactly what mem2reg decides. The fixture otherwise meets every other
/// promotion condition (one block, a store before the load, one type, no
/// proof metadata), so mem2reg promotes it iff it does not escape.
#[test]
fn the_escape_bit_is_mem2regs() {
    // %0 = a pointer parameter, %1 = a callable parameter; %2 = the alloca,
    // %3 = a constant, %4 = the loaded value.
    let shapes: Vec<(&str, Vec<InstrNode>, bool)> = vec![
        (
            "loads and stores only",
            vec![store(2, 3), load(5, 2)],
            false,
        ),
        ("gep", vec![gep(5, 2)], true),
        ("stored as a value", vec![store(0, 2)], true),
        ("stored into itself", vec![store(2, 2)], true),
        ("call argument", vec![call(5, &[2])], true),
        (
            "indirect call argument",
            vec![op(Inst::CallIndirect {
                callee: v(1),
                sig: FuncTyId::new(0),
                args: vs(&[2]),
                calling_conv: CallingConv::Rust,
            })],
            true,
        ),
        ("copy", vec![copy(5, 2)], true),
        ("cast", vec![cast(5, CastOp::PtrToInt, 2)], true),
        ("select arm", vec![select(5, 2, 0)], true),
        ("borrow", vec![at(5, Inst::Borrow { ptr: v(2) })], true),
        (
            "borrow mut",
            vec![at(5, Inst::BorrowMut { ptr: v(2) })],
            true,
        ),
        (
            "pointer data",
            vec![at(
                5,
                Inst::PtrData {
                    ptr_ty: Ty::Ptr,
                    ptr: v(2),
                },
            )],
            true,
        ),
        (
            "fat pointer data",
            vec![at(
                5,
                Inst::PtrFromParts {
                    ptr_ty: Ty::Ptr,
                    metadata_ty: Ty::Usize,
                    data: v(2),
                    metadata: v(3),
                },
            )],
            true,
        ),
        (
            "drop",
            vec![op(Inst::Drop {
                ty: Ty::I64,
                ptr: v(2),
            })],
            true,
        ),
        (
            "atomic load",
            vec![at(
                5,
                Inst::AtomicLoad {
                    ty: Ty::I64,
                    ptr: v(2),
                    ordering: Ordering::SeqCst,
                },
            )],
            true,
        ),
        (
            "atomic store",
            vec![op(Inst::AtomicStore {
                ty: Ty::I64,
                ptr: v(2),
                value: v(3),
                ordering: Ordering::SeqCst,
            })],
            true,
        ),
        (
            "atomic rmw",
            vec![at(
                5,
                Inst::AtomicRMW {
                    op: AtomicRMWOp::Add,
                    ty: Ty::I64,
                    ptr: v(2),
                    value: v(3),
                    ordering: Ordering::SeqCst,
                },
            )],
            true,
        ),
        (
            "memcopy destination",
            vec![op(Inst::MemCopy {
                dst: v(2),
                src: v(0),
                bytes: v(3),
                overlap: false,
            })],
            true,
        ),
        (
            "memcopy source",
            vec![op(Inst::MemCopy {
                dst: v(0),
                src: v(2),
                bytes: v(3),
                overlap: false,
            })],
            true,
        ),
        (
            "memset",
            vec![op(Inst::MemSet {
                dst: v(2),
                byte: v(3),
                bytes: v(3),
            })],
            true,
        ),
        ("dealloc", vec![op(Inst::Dealloc { ptr: v(2) })], true),
        (
            "aggregate lane",
            vec![at(
                5,
                Inst::MakeAggregate {
                    ty: Ty::Ptr,
                    variant: None,
                    fields: vs(&[2]),
                },
            )],
            true,
        ),
        (
            "inserted field",
            vec![at(
                5,
                Inst::InsertField {
                    ty: Ty::Ptr,
                    aggregate: v(0),
                    field: 0,
                    value: v(2),
                },
            )],
            true,
        ),
        (
            "dialect operand",
            vec![op(Inst::DialectOp(Box::new({
                let mut operation = DialectInst::new("opaque", "use");
                operation.operands.push(v(2));
                operation
            })))],
            true,
        ),
    ];
    let fixture = |shape: Vec<InstrNode>, terminator: InstrNode| {
        let mut body = vec![alloca(2), konst(3), store(2, 3), load(4, 2)];
        body.extend(shape);
        body.push(terminator);
        function(vec![
            block(0, &[0, 1], body),
            block(1, &[6], vec![ret(&[])]),
        ])
    };
    let mut cases: Vec<(String, Function, bool)> = shapes
        .into_iter()
        .map(|(name, shape, escapes)| (name.to_owned(), fixture(shape, ret(&[])), escapes))
        .collect();
    cases.push(("returned".into(), fixture(vec![], ret(&[2])), true));
    cases.push(("branch argument".into(), fixture(vec![], br(1, &[2])), true));
    cases.push((
        "invoke argument".into(),
        fixture(vec![], invoke(5, 1, &[2], 1)),
        true,
    ));
    for (name, f, escapes) in cases {
        let roots = pointer_roots(&f);
        assert_eq!(roots.escapes(v(2)), Some(escapes), "{name}");
        assert_eq!(roots.is_private(v(2)), !escapes, "{name}");
        let mut promoted = f.clone();
        assert_eq!(
            promote_allocas_function(&mut promoted) == 1,
            !escapes,
            "{name}: mem2reg disagrees"
        );
        assert_private_is_the_allocation(&f, &roots);
    }
}

/// The rule covers every allocation, counted and heap ones included, and
/// only allocations have an escape bit.
#[test]
fn every_allocation_has_an_escape_bit_and_only_allocations() {
    let f = function(vec![block(
        0,
        &[0],
        vec![
            konst(1),
            at(
                2,
                Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(v(1)),
                    align: None,
                },
            ),
            heap(3),
            heap(4),
            alloca(5),
            store(2, 1),
            load(6, 3),
            store(4, 1),
            call(7, &[4]),
            gep(8, 5),
            load(9, 8),
            ret(&[]),
        ],
    )]);
    let roots = pointer_roots(&f);
    assert_eq!(roots.escapes(v(2)), Some(false), "a counted alloca");
    assert_eq!(roots.escapes(v(3)), Some(false), "a heap allocation");
    assert_eq!(roots.escapes(v(4)), Some(true), "passed to a call");
    assert_eq!(roots.escapes(v(5)), Some(true), "a GEP base");
    assert!(roots.is_private(v(2)) && roots.is_private(v(3)));
    assert!(!roots.is_private(v(5)) && !roots.is_private(v(8)));
    assert_eq!(
        roots.root(v(8)),
        &locals(&[5]),
        "an escaped local is still Local"
    );
    for value in [0, 1, 6, 7, 8, 9, 1000] {
        assert_eq!(roots.escapes(v(value)), None, "%{value} is no allocation");
        assert!(!roots.is_private(v(value)));
    }
}

/// A use in a dead block, or after a terminator, still escapes: the bit is
/// over every stored instruction, as mem2reg's is.
#[test]
fn a_dead_use_still_escapes() {
    let f = function(vec![
        block(
            0,
            &[0],
            vec![alloca(1), store(1, 0), ret(&[]), call(2, &[1])],
        ),
        block(1, &[], vec![alloca(3), store(3, 0), ret(&[])]),
        block(2, &[], vec![call(4, &[3]), ret(&[])]),
    ]);
    let roots = pointer_roots(&f);
    assert_eq!(roots.escapes(v(1)), Some(true));
    assert_eq!(roots.escapes(v(3)), Some(true));
}
