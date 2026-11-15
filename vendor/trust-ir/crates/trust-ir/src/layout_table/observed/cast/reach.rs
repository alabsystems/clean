// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The three pure-disjunction reach predicates used by the cast rule.
//! A visited nominal node is expanded once per query, including all duplicate
//! definitions. Cycles and missing references add no seed, exactly as ReachMemo.
//! Borrowed lazy cursors avoid staging a wide table/tuple before its callbacks.
//! Definition tables use actual charged scans; ordinary indexes are not used.

use super::*;
use crate::ty::RecordDef;
use crate::type_reachability::{TableReferent, table_referent};

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Mode {
    Handle,
    Closure,
    Bool,
    Storage,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Entry(usize),
    Signature(usize),
    Struct(u32),
    Enum(u32),
    Record(u32),
    Closure(usize),
}
impl From<TableReferent> for Node {
    fn from(node: TableReferent) -> Self {
        match node {
            TableReferent::Ty(id) => Self::Entry(id),
            TableReferent::FuncTy(id) => Self::Signature(id),
            TableReferent::Struct(id) => Self::Struct(id),
            TableReferent::Enum(id) => Self::Enum(id),
            TableReferent::Record(id) => Self::Record(id),
            TableReferent::ClosureTy(id) => Self::Closure(id),
        }
    }
}

#[derive(Clone, Copy)]
enum Task<'a> {
    Type(&'a Ty),
    Types(&'a [Ty]),
    Fields(&'a [FieldDef]),
    Variants(&'a [EnumVariant]),
    Structs(&'a [StructDef], u32),
    Enums(&'a [EnumDef], u32),
    Records(&'a [RecordDef], u32),
    Node(Node),
}

pub(super) fn reaches<O: ExecutionObserver>(
    module: &Module,
    mode: Mode,
    root: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    let mut tasks = Vec::new();
    let mut seen = BTreeSet::new();
    let result = (|| {
        work.push(&mut tasks, Task::Type(root))?;
        while !tasks.is_empty() {
            work.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                Task::Type(ty) => {
                    if scan(mode, ty, &mut tasks, work)? {
                        return Ok(true);
                    }
                }
                Task::Node(node) => {
                    work.lookup(seen.len())?;
                    if seen.contains(&node) {
                        continue;
                    }
                    work.tree::<Node, ()>(seen.len())?;
                    seen.insert(node);
                    expand(module, mode, node, &mut tasks, work)?;
                }
                other => next(other, &mut tasks, work)?,
            }
        }
        Ok(false)
    })();
    work.retire_copy_vec(tasks);
    work.retire_set(seen);
    work.poll()?;
    result
}

fn scan<'a, O: ExecutionObserver>(
    mode: Mode,
    ty: &'a Ty,
    tasks: &mut Vec<Task<'a>>,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    if matches!(
        (mode, ty),
        (Mode::Handle, Ty::Handle(_))
            | (Mode::Closure, Ty::Closure(_))
            | (Mode::Bool, Ty::Bool)
            | (Mode::Storage, Ty::Storage(_))
    ) {
        return Ok(true);
    }
    // table_referent is a constant-size exhaustive outer-constructor match.
    // The by-value walks select only the original subset of those references.
    let follow = mode == Mode::Handle
        || matches!(
            ty,
            Ty::Array(_, _) | Ty::Refine(_, _) | Ty::Struct(_) | Ty::Enum(_)
        )
        || (mode == Mode::Closure && matches!(ty, Ty::Record(_)))
        || (mode == Mode::Storage
            && matches!(
                ty,
                Ty::Set(..) | Ty::Sequence(_) | Ty::Record(_) | Ty::Closure(_)
            ));
    if follow && let Some(node) = table_referent(ty) {
        work.push(tasks, Task::Node(node.into()))?;
    }
    match ty {
        Ty::Storage(_) => {}
        Ty::Tuple(types) => work.push(tasks, Task::Types(types))?,
        Ty::Vector(child, _) | Ty::Tensor(child, _) => work.push(tasks, Task::Type(child))?,
        Ty::Ref(child)
        | Ty::RefMut(child)
        | Ty::PtrConst(child)
        | Ty::PtrMut(child)
        | Ty::Rc(child) => {
            if mode == Mode::Handle {
                work.push(tasks, Task::Type(child))?;
            }
        }
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Ptr
        | Ty::FatPtr(_)
        | Ty::Unit
        | Ty::Never
        | Ty::Struct(_)
        | Ty::Array(_, _)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Set(_, _)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(_, _)
        | Ty::Dialect(_)
        | Ty::Handle(_) => {}
        Ty::Ext(extension) => extension.unreachable(),
    }
    Ok(false)
}

fn expand<'a, O: ExecutionObserver>(
    module: &'a Module,
    mode: Mode,
    node: Node,
    tasks: &mut Vec<Task<'a>>,
    work: &mut Work<'_, '_, O>,
) -> R {
    match node {
        Node::Entry(id) => {
            if let Some(ty) = module.types.get(id) {
                work.push(tasks, Task::Type(ty))?;
            }
        }
        Node::Signature(id) => {
            if let Some(sig) = module.func_types.get(id) {
                work.push(tasks, Task::Types(&sig.returns))?;
                work.push(tasks, Task::Types(&sig.params))?;
            }
        }
        Node::Struct(id) => work.push(tasks, Task::Structs(&module.structs, id))?,
        Node::Enum(id) => work.push(tasks, Task::Enums(&module.enums, id))?,
        Node::Record(id) => work.push(tasks, Task::Records(&module.records, id))?,
        Node::Closure(id) => {
            if let Some(closure) = module.closure_types.get(id) {
                if mode == Mode::Handle {
                    work.push(tasks, Task::Node(Node::Signature(closure.func.as_usize())))?;
                }
                work.push(tasks, Task::Types(&closure.captures))?;
            }
        }
    }
    Ok(())
}

fn next<'a, O: ExecutionObserver>(
    task: Task<'a>,
    tasks: &mut Vec<Task<'a>>,
    work: &mut Work<'_, '_, O>,
) -> R {
    match task {
        Task::Types(types) => {
            if let Some((first, rest)) = types.split_first() {
                work.push(tasks, Task::Types(rest))?;
                work.push(tasks, Task::Type(first))?;
            }
        }
        Task::Fields(fields) => {
            if let Some((first, rest)) = fields.split_first() {
                work.push(tasks, Task::Fields(rest))?;
                work.push(tasks, Task::Type(&first.ty))?;
            }
        }
        Task::Variants(variants) => {
            if let Some((first, rest)) = variants.split_first() {
                work.push(tasks, Task::Variants(rest))?;
                work.push(tasks, Task::Types(&first.fields))?;
            }
        }
        Task::Structs(defs, id) => {
            if let Some((first, rest)) = defs.split_first() {
                work.push(tasks, Task::Structs(rest, id))?;
                if first.id.index() == id {
                    work.push(tasks, Task::Fields(&first.fields))?;
                }
            }
        }
        Task::Enums(defs, id) => {
            if let Some((first, rest)) = defs.split_first() {
                work.push(tasks, Task::Enums(rest, id))?;
                if first.id.index() == id {
                    work.push(tasks, Task::Variants(&first.variants))?;
                }
            }
        }
        Task::Records(defs, id) => {
            if let Some((first, rest)) = defs.split_first() {
                work.push(tasks, Task::Records(rest, id))?;
                if first.id.index() == id {
                    work.push(tasks, Task::Fields(&first.fields))?;
                }
            }
        }
        Task::Type(_) | Task::Node(_) => {
            return Err(ObservedValueError::UnsupportedValue.into());
        }
    }
    Ok(())
}
