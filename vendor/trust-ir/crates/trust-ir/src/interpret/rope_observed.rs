// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fallible structural counterparts of the persistent rope operations.
//!
//! New nodes are held by `Build` until all fallible work has finished. Thus
//! unwinding an ordinary `Result` never makes a partial persistent tree's last
//! owner disappear through an unobserved recursive destructor.

use super::*;
use crate::interpret::observed::{
    ExecutionPhase, ObservedRopeElem, ObservedValueError, StructuralProgress,
};
use core::mem::size_of;

type Result<T> = core::result::Result<T, ObservedValueError>;

fn visit(p: &mut impl StructuralProgress) -> Result<()> {
    p.admit(ExecutionPhase::RopeNode, 1, 0)?;
    Ok(())
}

fn bytes<T>(count: usize) -> Result<usize> {
    count
        .checked_mul(size_of::<T>())
        .ok_or(ObservedValueError::CapacityOverflow)
}

fn reserve<T>(
    values: &mut Vec<T>,
    additional: usize,
    p: &mut impl StructuralProgress,
) -> Result<()> {
    let needed = values
        .len()
        .checked_add(additional)
        .ok_or(ObservedValueError::CapacityOverflow)?;
    if needed <= values.capacity() {
        return Ok(());
    }
    let capacity = needed
        .max(
            values
                .capacity()
                .checked_mul(2)
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )
        .max(4);
    // Price the replacement backing storage and its eventual drain before the
    // allocator can copy the existing buffer. This is a logical debit, not RSS.
    p.admit(
        ExecutionPhase::HostAllocation,
        capacity
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?,
        bytes::<T>(capacity)?,
    )?;
    values
        .try_reserve_exact(capacity - values.len())
        .map_err(|_| ObservedValueError::AllocationFailed)
}

fn retire_values<T: ObservedRopeElem>(mut values: Vec<T>, p: &mut impl StructuralProgress) {
    while let Some(value) = values.pop() {
        p.retirement_poll();
        value.retire_observed(p);
    }
    p.retirement_poll();
}

/// AVL height is at most twice log2(number of nonempty leaves), plus one.
/// A repeat's virtual balanced height obeys the same bound. With u64 lengths
/// this fixed frontier has room for every valid rope, without allocating after
/// refusal. It bounds representation height, never an input's logical length.
const RETIRE_FRONTIER: usize = 2 * u64::BITS as usize + 4;

fn retire_link<T: ObservedRopeElem>(root: Link<T>, p: &mut impl StructuralProgress) {
    let mut stack: [Option<Link<T>>; RETIRE_FRONTIER] = core::array::from_fn(|_| None);
    let mut count = 1;
    stack[0] = Some(root);
    while count != 0 {
        count -= 1;
        let Some(link) = stack[count].take() else {
            continue;
        };
        p.retirement_poll();
        // into_inner releases a shared reference without the try_unwrap/Err
        // race that can accidentally run a last-owner recursive destructor.
        let Some(node) = Arc::into_inner(link) else {
            continue;
        };
        match node.kind {
            Kind::Dense { data, .. } => {
                if let Some(values) = Arc::into_inner(data) {
                    retire_values(values, p);
                }
            }
            Kind::Uniform(value) => value.retire_observed(p),
            Kind::Repeat { unit, .. } => {
                stack[count] = Some(unit);
                count += 1;
            }
            Kind::Concat { left, right } => {
                stack[count] = Some(right);
                stack[count + 1] = Some(left);
                count += 2;
            }
        }
    }
    p.retirement_poll();
}

fn retire_kind<T: ObservedRopeElem>(kind: Kind<T>, p: &mut impl StructuralProgress) {
    match kind {
        Kind::Dense { data, .. } => {
            if let Some(values) = Arc::into_inner(data) {
                retire_values(values, p);
            }
        }
        Kind::Uniform(value) => value.retire_observed(p),
        Kind::Repeat { unit, .. } => retire_link(unit, p),
        Kind::Concat { left, right } => {
            retire_link(left, p);
            retire_link(right, p);
        }
    }
}

struct Build<T: ObservedRopeElem> {
    kept: Vec<Link<T>>,
}

impl<T: ObservedRopeElem> Build<T> {
    fn new() -> Self {
        Self { kept: Vec::new() }
    }

    fn node(
        &mut self,
        len: u64,
        height: u32,
        kind: Kind<T>,
        p: &mut impl StructuralProgress,
    ) -> Result<Link<T>> {
        let admission = (|| {
            reserve(&mut self.kept, 1, p)?;
            let allocation = size_of::<Node<T>>()
                .checked_add(2 * size_of::<usize>())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            // One construction and one eventual unique-node retirement.
            p.admit(ExecutionPhase::HostAllocation, 2, allocation)?;
            Ok(())
        })();
        if let Err(error) = admission {
            retire_kind(kind, p);
            return Err(error);
        }
        let node = Arc::new(Node { len, height, kind });
        self.kept.push(Arc::clone(&node));
        Ok(node)
    }

    fn uniform(&mut self, value: T, len: u64, p: &mut impl StructuralProgress) -> Result<Link<T>> {
        self.node(len, 0, Kind::Uniform(value), p)
    }

    fn dense(&mut self, values: Vec<T>, p: &mut impl StructuralProgress) -> Result<Link<T>> {
        let len = match u64::try_from(values.len()) {
            Ok(len) => len,
            Err(_) => {
                retire_values(values, p);
                return Err(ObservedValueError::CapacityOverflow);
            }
        };
        if let Err(error) = p.admit(
            ExecutionPhase::HostAllocation,
            values.len(),
            size_of::<Vec<T>>() + 2 * size_of::<usize>(),
        ) {
            retire_values(values, p);
            return Err(error.into());
        }
        self.node(
            len,
            0,
            Kind::Dense {
                data: Arc::new(values),
                start: 0,
            },
            p,
        )
    }

    fn concat(
        &mut self,
        left: &Link<T>,
        right: &Link<T>,
        p: &mut impl StructuralProgress,
    ) -> Result<Link<T>> {
        let len = left
            .len
            .checked_add(right.len)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let height = left
            .height
            .max(right.height)
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.node(
            len,
            height,
            Kind::Concat {
                left: Arc::clone(left),
                right: Arc::clone(right),
            },
            p,
        )
    }

    fn retire(mut self, p: &mut impl StructuralProgress) {
        while let Some(node) = self.kept.pop() {
            retire_link(node, p);
        }
        p.retirement_poll();
    }
}

fn finish<T: ObservedRopeElem>(
    build: Build<T>,
    result: Result<Option<Link<T>>>,
    p: &mut impl StructuralProgress,
) -> Result<Rope<T>> {
    build.retire(p);
    let publication = p.admit(ExecutionPhase::RopeNode, 0, 0);
    match (result, publication) {
        (Ok(root), Ok(())) => Ok(Rope { root }),
        (Ok(root), Err(error)) => {
            if let Some(root) = root {
                retire_link(root, p);
            }
            Err(error.into())
        }
        (Err(_), Err(error)) => Err(error.into()),
        (Err(error), Ok(())) => Err(error),
    }
}

fn same_node_observed<T: ObservedRopeElem>(
    a: &Link<T>,
    b: &Link<T>,
    p: &mut impl StructuralProgress,
) -> Result<bool> {
    visit(p)?;
    if Arc::ptr_eq(a, b) {
        return Ok(true);
    }
    if a.len != b.len {
        return Ok(false);
    }
    match (&a.kind, &b.kind) {
        (Kind::Dense { data: x, start: i }, Kind::Dense { data: y, start: j }) => {
            Ok(Arc::ptr_eq(x, y) && i == j)
        }
        (Kind::Uniform(x), Kind::Uniform(y)) => x.same_observed(y, p),
        (Kind::Repeat { unit: u, count: c }, Kind::Repeat { unit: v, count: d }) => {
            if c == d {
                same_node_observed(u, v, p)
            } else {
                Ok(false)
            }
        }
        (
            Kind::Concat {
                left: al,
                right: ar,
            },
            Kind::Concat {
                left: bl,
                right: br,
            },
        ) => Ok(Arc::ptr_eq(al, bl) && Arc::ptr_eq(ar, br)),
        _ => Ok(false),
    }
}

fn repeat_node_observed<T: ObservedRopeElem>(
    unit: &Link<T>,
    count: u64,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Option<Link<T>>> {
    visit(p)?;
    if count == 0 {
        return Ok(None);
    }
    if count == 1 {
        return Ok(Some(Arc::clone(unit)));
    }
    let len = unit
        .len
        .checked_mul(count)
        .ok_or(ObservedValueError::CapacityOverflow)?;
    let result = match &unit.kind {
        Kind::Uniform(value) => build.uniform(value.clone_observed(p)?, len, p)?,
        Kind::Dense { data, start } if unit.len == 1 => {
            build.uniform(data[*start].clone_observed(p)?, len, p)?
        }
        Kind::Repeat {
            unit: inner,
            count: inner_count,
        } => {
            let count = inner_count
                .checked_mul(count)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let height = inner
                .height
                .checked_add(ceil_log2(count))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            build.node(
                len,
                height,
                Kind::Repeat {
                    unit: Arc::clone(inner),
                    count,
                },
                p,
            )?
        }
        _ => {
            let height = unit
                .height
                .checked_add(ceil_log2(count))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            build.node(
                len,
                height,
                Kind::Repeat {
                    unit: Arc::clone(unit),
                    count,
                },
                p,
            )?
        }
    };
    Ok(Some(result))
}

fn expose_observed<T: ObservedRopeElem>(
    node: &Link<T>,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<(Link<T>, Link<T>)> {
    visit(p)?;
    match &node.kind {
        Kind::Concat { left, right } => Ok((Arc::clone(left), Arc::clone(right))),
        Kind::Repeat { unit, count } => {
            let first = count.div_ceil(2);
            let left = repeat_node_observed(unit, first, build, p)?
                .ok_or(ObservedValueError::InvalidRange)?;
            let right = repeat_node_observed(unit, count - first, build, p)?
                .ok_or(ObservedValueError::InvalidRange)?;
            Ok((left, right))
        }
        _ => Err(ObservedValueError::InvalidRange),
    }
}

fn rotate_left_observed<T: ObservedRopeElem>(
    node: &Link<T>,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Link<T>> {
    let (left, right) = expose_observed(node, build, p)?;
    let (middle, last) = expose_observed(&right, build, p)?;
    let first = build.concat(&left, &middle, p)?;
    build.concat(&first, &last, p)
}

fn rotate_right_observed<T: ObservedRopeElem>(
    node: &Link<T>,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Link<T>> {
    let (left, right) = expose_observed(node, build, p)?;
    let (first, middle) = expose_observed(&left, build, p)?;
    let last = build.concat(&middle, &right, p)?;
    build.concat(&first, &last, p)
}

fn merge_observed<T: ObservedRopeElem>(
    a: &Link<T>,
    b: &Link<T>,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Option<Link<T>>> {
    let (ua, ca) = unit_and_count(a);
    let (ub, cb) = unit_and_count(b);
    if same_node_observed(ua, ub, p)? {
        return repeat_node_observed(
            ua,
            ca.checked_add(cb)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            build,
            p,
        );
    }
    if let (Kind::Uniform(x), Kind::Uniform(y)) = (&a.kind, &b.kind)
        && x.same_observed(y, p)?
    {
        let len = a
            .len
            .checked_add(b.len)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        return build.uniform(x.clone_observed(p)?, len, p).map(Some);
    }
    if let (Kind::Dense { data: x, start: i }, Kind::Dense { data: y, start: j }) =
        (&a.kind, &b.kind)
    {
        let total = a
            .len
            .checked_add(b.len)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if total <= SMALL_LEAF as u64 {
            let mut values = Vec::new();
            let copied = (|| {
                reserve(&mut values, total as usize, p)?;
                for value in x[*i..*i + a.len as usize]
                    .iter()
                    .chain(&y[*j..*j + b.len as usize])
                {
                    p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
                    values.push(value.clone_observed(p)?);
                }
                Ok(())
            })();
            if let Err(error) = copied {
                retire_values(values, p);
                return Err(error);
            }
            return build.dense(values, p).map(Some);
        }
    }
    Ok(None)
}

fn join_right_observed<T: ObservedRopeElem>(
    a: &Link<T>,
    b: &Link<T>,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Link<T>> {
    let (left, right) = expose_observed(a, build, p)?;
    let lh = left.height;
    if right.height <= b.height + 1 {
        let joined = build.concat(&right, b, p)?;
        if joined.height <= lh + 1 {
            build.concat(&left, &joined, p)
        } else {
            let rotated = rotate_right_observed(&joined, build, p)?;
            let node = build.concat(&left, &rotated, p)?;
            rotate_left_observed(&node, build, p)
        }
    } else {
        let joined = join_right_observed(&right, b, build, p)?;
        let jh = joined.height;
        let node = build.concat(&left, &joined, p)?;
        if jh <= lh + 1 {
            Ok(node)
        } else {
            rotate_left_observed(&node, build, p)
        }
    }
}

fn join_left_observed<T: ObservedRopeElem>(
    a: &Link<T>,
    b: &Link<T>,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Link<T>> {
    let (left, right) = expose_observed(b, build, p)?;
    let rh = right.height;
    if left.height <= a.height + 1 {
        let joined = build.concat(a, &left, p)?;
        if joined.height <= rh + 1 {
            build.concat(&joined, &right, p)
        } else {
            let rotated = rotate_left_observed(&joined, build, p)?;
            let node = build.concat(&rotated, &right, p)?;
            rotate_right_observed(&node, build, p)
        }
    } else {
        let joined = join_left_observed(a, &left, build, p)?;
        let jh = joined.height;
        let node = build.concat(&joined, &right, p)?;
        if jh <= rh + 1 {
            Ok(node)
        } else {
            rotate_right_observed(&node, build, p)
        }
    }
}

fn join_observed<T: ObservedRopeElem>(
    a: &Link<T>,
    b: &Link<T>,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Link<T>> {
    visit(p)?;
    if let Some(merged) = merge_observed(a, b, build, p)? {
        return Ok(merged);
    }
    if a.height > b.height + 1 {
        join_right_observed(a, b, build, p)
    } else if b.height > a.height + 1 {
        join_left_observed(a, b, build, p)
    } else {
        build.concat(a, b, p)
    }
}

fn join_opt_observed<T: ObservedRopeElem>(
    a: Option<Link<T>>,
    b: Option<Link<T>>,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Option<Link<T>>> {
    match (a, b) {
        (Some(a), Some(b)) => join_observed(&a, &b, build, p).map(Some),
        (a, None) => Ok(a),
        (None, b) => Ok(b),
    }
}

fn slice_node_observed<T: ObservedRopeElem>(
    node: &Link<T>,
    start: u64,
    len: u64,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Option<Link<T>>> {
    visit(p)?;
    if len == 0 {
        return Ok(None);
    }
    let end = start
        .checked_add(len)
        .ok_or(ObservedValueError::InvalidRange)?;
    if end > node.len {
        return Err(ObservedValueError::InvalidRange);
    }
    if start == 0 && len == node.len {
        return Ok(Some(Arc::clone(node)));
    }
    let root = match &node.kind {
        Kind::Dense { data, start: base } => {
            let offset =
                usize::try_from(start).map_err(|_| ObservedValueError::CapacityOverflow)?;
            let base = base
                .checked_add(offset)
                .ok_or(ObservedValueError::CapacityOverflow)?;
            build.node(
                len,
                0,
                Kind::Dense {
                    data: Arc::clone(data),
                    start: base,
                },
                p,
            )?
        }
        Kind::Uniform(value) => build.uniform(value.clone_observed(p)?, len, p)?,
        Kind::Repeat { unit, .. } => {
            let phase = start % unit.len;
            let head_len = if phase == 0 {
                0
            } else {
                (unit.len - phase).min(len)
            };
            let head = slice_node_observed(unit, phase, head_len, build, p)?;
            let remaining = len - head_len;
            let whole = remaining / unit.len;
            let middle = repeat_node_observed(unit, whole, build, p)?;
            let tail = slice_node_observed(unit, 0, remaining % unit.len, build, p)?;
            let first = join_opt_observed(head, middle, build, p)?;
            return join_opt_observed(first, tail, build, p);
        }
        Kind::Concat { left, right } => {
            if end <= left.len {
                return slice_node_observed(left, start, len, build, p);
            }
            if start >= left.len {
                return slice_node_observed(right, start - left.len, len, build, p);
            }
            let first = slice_node_observed(left, start, left.len - start, build, p)?;
            let last = slice_node_observed(right, 0, end - left.len, build, p)?;
            return join_opt_observed(first, last, build, p);
        }
    };
    Ok(Some(root))
}

fn set_node_observed<T: ObservedRopeElem>(
    node: &Link<T>,
    index: u64,
    value: &T,
    build: &mut Build<T>,
    p: &mut impl StructuralProgress,
) -> Result<Link<T>> {
    visit(p)?;
    match &node.kind {
        Kind::Dense { data, start } => {
            let len =
                usize::try_from(node.len).map_err(|_| ObservedValueError::CapacityOverflow)?;
            let at = usize::try_from(index).map_err(|_| ObservedValueError::InvalidRange)?;
            let mut values = Vec::new();
            let copied = (|| {
                reserve(&mut values, len, p)?;
                for offset in 0..len {
                    p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
                    let element = if offset == at {
                        value
                    } else {
                        &data[*start + offset]
                    };
                    values.push(element.clone_observed(p)?);
                }
                Ok(())
            })();
            if let Err(error) = copied {
                retire_values(values, p);
                return Err(error);
            }
            build.dense(values, p)
        }
        Kind::Uniform(current) => {
            if current.same_observed(value, p)? {
                return Ok(Arc::clone(node));
            }
            let first = if index == 0 {
                None
            } else {
                Some(build.uniform(current.clone_observed(p)?, index, p)?)
            };
            let mut values = Vec::new();
            reserve(&mut values, 1, p)?;
            values.push(value.clone_observed(p)?);
            let middle = build.dense(values, p)?;
            let after = node.len - index - 1;
            let last = if after == 0 {
                None
            } else {
                Some(build.uniform(current.clone_observed(p)?, after, p)?)
            };
            let joined = join_opt_observed(first, Some(middle), build, p)?;
            join_opt_observed(joined, last, build, p)?.ok_or(ObservedValueError::InvalidRange)
        }
        Kind::Repeat { unit, count } => {
            let copy = index / unit.len;
            let first = repeat_node_observed(unit, copy, build, p)?;
            let middle = set_node_observed(unit, index % unit.len, value, build, p)?;
            let last = repeat_node_observed(unit, count - copy - 1, build, p)?;
            let joined = join_opt_observed(first, Some(middle), build, p)?;
            join_opt_observed(joined, last, build, p)?.ok_or(ObservedValueError::InvalidRange)
        }
        Kind::Concat { left, right } => {
            if index < left.len {
                let changed = set_node_observed(left, index, value, build, p)?;
                join_observed(&changed, right, build, p)
            } else {
                let changed = set_node_observed(right, index - left.len, value, build, p)?;
                join_observed(left, &changed, build, p)
            }
        }
    }
}

fn memo_reserve<K, V>(memo: &mut HashMap<K, V>, p: &mut impl StructuralProgress) -> Result<()>
where
    K: core::hash::Hash + Eq,
{
    if memo.len() == memo.capacity() {
        let population = memo
            .len()
            .checked_add(1)
            .and_then(|n| n.checked_mul(4))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let allocation = bytes::<(K, V)>(population)?
            .checked_add(population)
            .and_then(|n| n.checked_add(64))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        p.admit(ExecutionPhase::HostAllocation, population, allocation)?;
        memo.try_reserve(1)
            .map_err(|_| ObservedValueError::AllocationFailed)?;
    }
    Ok(())
}

fn map_node_observed<T: ObservedRopeElem, U: ObservedRopeElem, P: StructuralProgress>(
    node: &Link<T>,
    p: &mut P,
    map: &mut impl FnMut(&T, &mut P) -> Result<U>,
    memo: &mut HashMap<usize, Link<U>>,
    build: &mut Build<U>,
) -> Result<Link<U>> {
    visit(p)?;
    // Price a worst-case table probe before entering std's bounded table
    // operation. Both memo hits and misses are original-owner events.
    p.admit(
        ExecutionPhase::RopeNode,
        memo.capacity()
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?,
        0,
    )?;
    if let Some(done) = memo.get(&key(node)) {
        return Ok(Arc::clone(done));
    }
    let mapped = match &node.kind {
        Kind::Dense { data, start } => {
            let len =
                usize::try_from(node.len).map_err(|_| ObservedValueError::CapacityOverflow)?;
            let mut values = Vec::new();
            let converted = (|| {
                reserve(&mut values, len, p)?;
                for value in &data[*start..*start + len] {
                    p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
                    values.push(map(value, p)?);
                }
                Ok(())
            })();
            if let Err(error) = converted {
                retire_values(values, p);
                return Err(error);
            }
            build.dense(values, p)?
        }
        Kind::Uniform(value) => build.uniform(map(value, p)?, node.len, p)?,
        Kind::Repeat { unit, count } => {
            let mapped = map_node_observed(unit, p, map, memo, build)?;
            repeat_node_observed(&mapped, *count, build, p)?
                .ok_or(ObservedValueError::InvalidRange)?
        }
        Kind::Concat { left, right } => {
            let left = map_node_observed(left, p, map, memo, build)?;
            let right = map_node_observed(right, p, map, memo, build)?;
            join_observed(&left, &right, build, p)?
        }
    };
    memo_reserve(memo, p)?;
    p.admit(
        ExecutionPhase::RopeNode,
        memo.capacity()
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?,
        0,
    )?;
    memo.insert(key(node), Arc::clone(&mapped));
    Ok(mapped)
}

impl<T: ObservedRopeElem> Rope<T> {
    pub(crate) fn clone_observed(&self, p: &mut impl StructuralProgress) -> Result<Self> {
        visit(p)?;
        Ok(Self {
            root: self.root.clone(),
        })
    }

    pub(crate) fn uniform_observed(
        value: T,
        len: u64,
        p: &mut impl StructuralProgress,
    ) -> Result<Self> {
        if let Err(error) = visit(p) {
            value.retire_observed(p);
            return Err(error);
        }
        let mut build = Build::new();
        let result = if len == 0 {
            value.retire_observed(p);
            Ok(None)
        } else {
            build.uniform(value, len, p).map(Some)
        };
        finish(build, result, p)
    }

    /// Move a caller-owned literal buffer into bounded fresh leaves. Every
    /// physical element is visited; a logical uniform extent never enters here.
    pub(crate) fn dense_observed(values: Vec<T>, p: &mut impl StructuralProgress) -> Result<Self> {
        if let Err(error) = visit(p) {
            retire_values(values, p);
            return Err(error);
        }
        if T::FRESH_LEAF == 0 {
            retire_values(values, p);
            return Err(ObservedValueError::UnsupportedValue);
        }
        let mut elements = values.into_iter();
        let mut pending = Vec::new();
        let mut build = Build::new();
        let result = (|| {
            let mut root = None;
            loop {
                p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
                let Some(value) = elements.next() else { break };
                if let Err(error) = reserve(&mut pending, 1, p) {
                    value.retire_observed(p);
                    return Err(error);
                }
                pending.push(value);
                if pending.len() == T::FRESH_LEAF {
                    let leaf = build.dense(core::mem::take(&mut pending), p)?;
                    root = join_opt_observed(root, Some(leaf), &mut build, p)?;
                }
            }
            if !pending.is_empty() {
                let leaf = build.dense(core::mem::take(&mut pending), p)?;
                root = join_opt_observed(root, Some(leaf), &mut build, p)?;
            }
            Ok(root)
        })();
        retire_values(pending, p);
        for value in elements {
            p.retirement_poll();
            value.retire_observed(p);
        }
        finish(build, result, p)
    }

    pub(crate) fn get_observed(
        &self,
        mut index: u64,
        p: &mut impl StructuralProgress,
    ) -> Result<Option<&T>> {
        visit(p)?;
        let Some(mut node) = self.root.as_deref() else {
            return Ok(None);
        };
        if index >= node.len {
            return Ok(None);
        }
        loop {
            visit(p)?;
            match &node.kind {
                Kind::Dense { data, start } => {
                    let at =
                        usize::try_from(index).map_err(|_| ObservedValueError::CapacityOverflow)?;
                    let offset = start
                        .checked_add(at)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    p.admit(ExecutionPhase::RopeNode, 0, 0)?;
                    return Ok(data.get(offset));
                }
                Kind::Uniform(value) => {
                    p.admit(ExecutionPhase::RopeNode, 0, 0)?;
                    return Ok(Some(value));
                }
                Kind::Repeat { unit, .. } => {
                    index %= unit.len;
                    node = unit;
                }
                Kind::Concat { left, right } => {
                    if index < left.len {
                        node = left;
                    } else {
                        index -= left.len;
                        node = right;
                    }
                }
            }
        }
    }

    pub(crate) fn set_observed(
        &self,
        index: u64,
        value: T,
        p: &mut impl StructuralProgress,
    ) -> Result<Self> {
        if let Err(error) = visit(p) {
            value.retire_observed(p);
            return Err(error);
        }
        let mut build = Build::new();
        let result = match &self.root {
            Some(root) if index < root.len => {
                set_node_observed(root, index, &value, &mut build, p).map(Some)
            }
            _ => Err(ObservedValueError::InvalidRange),
        };
        value.retire_observed(p);
        finish(build, result, p)
    }

    pub(crate) fn slice_observed(
        &self,
        start: u64,
        len: u64,
        p: &mut impl StructuralProgress,
    ) -> Result<Self> {
        visit(p)?;
        if start.checked_add(len).is_none_or(|end| end > self.len()) {
            return Err(ObservedValueError::InvalidRange);
        }
        let mut build = Build::new();
        let result = match &self.root {
            Some(root) => slice_node_observed(root, start, len, &mut build, p),
            None => Ok(None),
        };
        finish(build, result, p)
    }

    pub(crate) fn concat_observed(
        parts: Vec<Self>,
        p: &mut impl StructuralProgress,
    ) -> Result<Self> {
        let mut build = Build::new();
        let result = (|| {
            visit(p)?;
            let mut result = None;
            for part in &parts {
                visit(p)?;
                result = join_opt_observed(result, part.root.clone(), &mut build, p)?;
            }
            Ok(result)
        })();
        // Parts remain alive throughout construction, including error returns.
        for part in parts {
            part.retire_observed(p);
        }
        finish(build, result, p)
    }

    #[cfg(test)]
    pub(crate) fn repeat_observed(
        &self,
        count: u64,
        p: &mut impl StructuralProgress,
    ) -> Result<Self> {
        visit(p)?;
        let mut build = Build::new();
        let result = (|| {
            let Some(root) = &self.root else {
                return Ok(None);
            };
            if count > 1
                && let Some(value) = self.all_same_observed(p)?
            {
                let len = root
                    .len
                    .checked_mul(count)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                return build.uniform(value.clone_observed(p)?, len, p).map(Some);
            }
            repeat_node_observed(root, count, &mut build, p)
        })();
        finish(build, result, p)
    }

    pub(crate) fn try_map_observed<U: ObservedRopeElem, P: StructuralProgress>(
        &self,
        p: &mut P,
        mut map: impl FnMut(&T, &mut P) -> Result<U>,
    ) -> Result<Rope<U>> {
        visit(p)?;
        let mut build = Build::new();
        let mut memo = HashMap::new();
        let result = match &self.root {
            Some(root) => map_node_observed(root, p, &mut map, &mut memo, &mut build).map(Some),
            None => Ok(None),
        };
        {
            let mut entries = memo.drain();
            loop {
                p.retirement_poll();
                let Some((_, node)) = entries.next() else {
                    break;
                };
                retire_link(node, p);
            }
        }
        drop(memo);
        p.retirement_poll();
        finish(build, result, p)
    }

    pub(crate) fn try_for_each_stored_observed<P: StructuralProgress>(
        &self,
        p: &mut P,
        mut visit_element: impl FnMut(&T, &mut P) -> Result<()>,
    ) -> Result<()> {
        visit(p)?;
        let mut seen = HashSet::new();
        let mut stack = Vec::new();
        let result: Result<()> = (|| {
            if let Some(root) = &self.root {
                reserve(&mut stack, 1, p)?;
                stack.push(root);
            }
            while let Some(node) = stack.pop() {
                visit(p)?;
                p.admit(
                    ExecutionPhase::RopeNode,
                    seen.capacity()
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?,
                    0,
                )?;
                if seen.len() == seen.capacity() {
                    let population = seen
                        .len()
                        .checked_add(1)
                        .and_then(|n| n.checked_mul(4))
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    p.admit(
                        ExecutionPhase::HostAllocation,
                        population,
                        bytes::<usize>(population)?
                            .checked_add(population)
                            .and_then(|n| n.checked_add(64))
                            .ok_or(ObservedValueError::CapacityOverflow)?,
                    )?;
                    seen.try_reserve(1)
                        .map_err(|_| ObservedValueError::AllocationFailed)?;
                }
                if !seen.insert(key(node)) {
                    continue;
                }
                match &node.kind {
                    Kind::Uniform(value) => visit_element(value, p)?,
                    Kind::Dense { data, start } => {
                        let len = usize::try_from(node.len)
                            .map_err(|_| ObservedValueError::CapacityOverflow)?;
                        for element in &data[*start..*start + len] {
                            p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
                            visit_element(element, p)?;
                        }
                    }
                    Kind::Repeat { unit, .. } => {
                        reserve(&mut stack, 1, p)?;
                        stack.push(unit);
                    }
                    Kind::Concat { left, right } => {
                        reserve(&mut stack, 2, p)?;
                        stack.push(right);
                        stack.push(left);
                    }
                }
            }
            Ok(())
        })();
        while !stack.is_empty() {
            p.retirement_poll();
            stack.pop();
        }
        drop(stack);
        {
            let mut entries = seen.drain();
            loop {
                p.retirement_poll();
                if entries.next().is_none() {
                    break;
                }
            }
        }
        drop(seen);
        p.retirement_poll();
        result?;
        p.admit(ExecutionPhase::RopeNode, 0, 0)?;
        Ok(())
    }

    /// Observe the literal-window COW before returning its mutable slice. The
    /// caller must observe every actual overwrite through that slice as well.
    pub(crate) fn dense_mut_observed(
        &mut self,
        p: &mut impl StructuralProgress,
    ) -> Result<Option<&mut [T]>> {
        visit(p)?;
        let dense = self
            .root
            .as_ref()
            .is_some_and(|root| matches!(root.kind, Kind::Dense { .. }));
        if !dense {
            return Ok(None);
        }
        let unique = self
            .root
            .as_mut()
            .and_then(Arc::get_mut)
            .is_some_and(|node| match &mut node.kind {
                Kind::Dense { data, .. } => Arc::get_mut(data).is_some(),
                _ => false,
            });
        if !unique {
            let replacement = self.try_map_observed(p, |value, p| value.clone_observed(p))?;
            let old = core::mem::replace(self, replacement);
            old.retire_observed(p);
        }
        p.admit(ExecutionPhase::RopeNode, 0, 0)?;
        let root = self.root.as_mut().ok_or(ObservedValueError::InvalidRange)?;
        let node = Arc::get_mut(root).ok_or(ObservedValueError::UnsupportedValue)?;
        let len = usize::try_from(node.len).map_err(|_| ObservedValueError::CapacityOverflow)?;
        let Kind::Dense { data, start } = &mut node.kind else {
            return Err(ObservedValueError::UnsupportedValue);
        };
        let buffer = Arc::get_mut(data).ok_or(ObservedValueError::UnsupportedValue)?;
        let end = start
            .checked_add(len)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(buffer.get_mut(*start..end))
    }

    pub(crate) fn try_append_in_place_observed(
        &mut self,
        elements: &[T],
        p: &mut impl StructuralProgress,
    ) -> Result<bool> {
        visit(p)?;
        let Some(node) = self.root.as_mut().and_then(Arc::get_mut) else {
            return Ok(false);
        };
        let Kind::Dense { data, start } = &mut node.kind else {
            return Ok(false);
        };
        let Some(buffer) = Arc::get_mut(data) else {
            return Ok(false);
        };
        let len = usize::try_from(node.len).map_err(|_| ObservedValueError::CapacityOverflow)?;
        if start.checked_add(len) != Some(buffer.len()) {
            return Ok(false);
        }
        let added =
            u64::try_from(elements.len()).map_err(|_| ObservedValueError::CapacityOverflow)?;
        let new_len = node
            .len
            .checked_add(added)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let previous = buffer.len();
        reserve(buffer, elements.len(), p)?;
        let appended = (|| {
            for element in elements {
                p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
                buffer.push(element.clone_observed(p)?);
            }
            p.admit(ExecutionPhase::RopeNode, 0, 0)?;
            Ok(())
        })();
        if let Err(error) = appended {
            while buffer.len() > previous {
                p.retirement_poll();
                if let Some(value) = buffer.pop() {
                    value.retire_observed(p);
                }
            }
            return Err(error);
        }
        node.len = new_len;
        Ok(true)
    }

    pub(crate) fn retire_observed(self, p: &mut impl StructuralProgress) {
        if let Some(root) = self.root {
            retire_link(root, p);
        }
        p.retirement_poll();
    }
}

impl<T: ObservedRopeElem> Rope<T> {
    #[allow(
        dead_code,
        reason = "staged by the observed-r23 lane with no production caller yet; its tests drive it"
    )]
    pub(crate) fn all_same_observed(&self, p: &mut impl StructuralProgress) -> Result<Option<&T>> {
        fn go<'a, T: ObservedRopeElem>(
            node: &'a Link<T>,
            p: &mut impl StructuralProgress,
            memo: &mut HashMap<usize, Option<&'a T>>,
        ) -> Result<Option<&'a T>> {
            visit(p)?;
            p.admit(
                ExecutionPhase::RopeNode,
                memo.capacity()
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                0,
            )?;
            if let Some(done) = memo.get(&key(node)) {
                return Ok(*done);
            }
            let answer = match &node.kind {
                Kind::Uniform(value) => Some(value),
                Kind::Dense { data, start } => {
                    let len = usize::try_from(node.len)
                        .map_err(|_| ObservedValueError::CapacityOverflow)?;
                    let values = &data[*start..*start + len];
                    let Some(first) = values.first() else {
                        return Err(ObservedValueError::InvalidRange);
                    };
                    let mut answer = Some(first);
                    for value in values {
                        p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
                        if !first.same_observed(value, p)? {
                            answer = None;
                            break;
                        }
                    }
                    answer
                }
                Kind::Repeat { unit, .. } => go(unit, p, memo)?,
                Kind::Concat { left, right } => match (go(left, p, memo)?, go(right, p, memo)?) {
                    (Some(a), Some(b)) if a.same_observed(b, p)? => Some(a),
                    _ => None,
                },
            };
            memo_reserve(memo, p)?;
            p.admit(
                ExecutionPhase::RopeNode,
                memo.capacity()
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?,
                0,
            )?;
            memo.insert(key(node), answer);
            Ok(answer)
        }
        visit(p)?;
        let mut memo = HashMap::new();
        let result = match &self.root {
            Some(root) => go(root, p, &mut memo),
            None => Ok(None),
        };
        {
            let mut entries = memo.drain();
            loop {
                p.retirement_poll();
                if entries.next().is_none() {
                    break;
                }
            }
        }
        drop(memo);
        p.retirement_poll();
        p.admit(ExecutionPhase::RopeNode, 0, 0)?;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpret::observed::ObservationStopped;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Default)]
    struct Progress {
        work: usize,
        copies: usize,
        limit: Option<usize>,
        copy_limit: Option<usize>,
        stopped: bool,
        retirement_polls: usize,
    }

    impl StructuralProgress for Progress {
        fn admit(
            &mut self,
            _: ExecutionPhase,
            work: usize,
            copies: usize,
        ) -> core::result::Result<(), ObservationStopped> {
            if self.stopped {
                return Err(ObservationStopped);
            }
            if self
                .limit
                .is_some_and(|limit| self.work.saturating_add(work) > limit)
                || self
                    .copy_limit
                    .is_some_and(|limit| self.copies.saturating_add(copies) > limit)
            {
                self.stopped = true;
                return Err(ObservationStopped);
            }
            self.work += work;
            self.copies += copies;
            Ok(())
        }
        fn retirement_poll(&mut self) {
            self.retirement_polls += 1;
        }
    }

    #[test]
    fn observed_maximum_extent_set_slice_and_map_are_structural() {
        let mut p = Progress::default();
        let original = Rope::uniform_observed(Some(3u8), u64::MAX, &mut p).unwrap();
        let changed = original
            .set_observed(u64::MAX - 1, Some(9), &mut p)
            .unwrap();
        assert_eq!(
            original.get_observed(u64::MAX - 1, &mut p).unwrap(),
            Some(&Some(3))
        );
        assert_eq!(
            changed.get_observed(u64::MAX - 1, &mut p).unwrap(),
            Some(&Some(9))
        );
        let tail = changed.slice_observed(u64::MAX - 3, 3, &mut p).unwrap();
        let mut calls = 0;
        let mapped = changed
            .try_map_observed(&mut p, |value, _| {
                calls += 1;
                Ok(value.map(|byte| byte + 1))
            })
            .unwrap();
        assert_eq!(calls, 2, "one stored uniform and one changed element");
        assert_eq!(
            mapped.get_observed(u64::MAX - 1, &mut p).unwrap(),
            Some(&Some(10))
        );
        assert!(changed.node_count() <= 4);
        assert!(p.work < 10_000);
        tail.retire_observed(&mut p);
        mapped.retire_observed(&mut p);
        changed.retire_observed(&mut p);
        original.retire_observed(&mut p);
    }

    #[test]
    fn observed_repeat_maps_the_stored_period_and_preserves_uniform_normalization() {
        let mut p = Progress::default();
        let unit = Rope::dense_observed(vec![Some(1u8), None, Some(2)], &mut p).unwrap();
        let repeated = unit.repeat_observed(u64::MAX / 3, &mut p).unwrap();
        let mut calls = 0;
        let mapped = repeated
            .try_map_observed(&mut p, |value, _| {
                calls += 1;
                Ok(value.unwrap_or(0).checked_add(1))
            })
            .unwrap();
        assert_eq!(calls, 3);
        assert_eq!(mapped.len(), u64::MAX);
        assert!(mapped.node_count() <= 2);
        let equal = Rope::dense_observed(vec![Some(7u8); 4], &mut p).unwrap();
        let uniform = equal.repeat_observed(1 << 50, &mut p).unwrap();
        assert_eq!(uniform.node_count(), 1);
        assert_eq!(uniform.as_uniform(), Some(&Some(7)));
        uniform.retire_observed(&mut p);
        equal.retire_observed(&mut p);
        mapped.retire_observed(&mut p);
        repeated.retire_observed(&mut p);
        unit.retire_observed(&mut p);
    }

    #[test]
    fn observed_overflow_is_incapacity_and_does_not_modify_the_input() {
        let mut p = Progress::default();
        let value = Rope::uniform_observed(Some(1u8), u64::MAX, &mut p).unwrap();
        assert!(matches!(
            value.repeat_observed(2, &mut p),
            Err(ObservedValueError::CapacityOverflow)
        ));
        assert_eq!(value.len(), u64::MAX);
        assert!(matches!(
            value.slice_observed(u64::MAX, 1, &mut p),
            Err(ObservedValueError::InvalidRange)
        ));
        value.retire_observed(&mut p);
    }

    #[derive(Clone)]
    struct Tracked {
        value: u8,
        born: Arc<AtomicUsize>,
        retired: Arc<AtomicUsize>,
    }
    impl Tracked {
        fn new(value: u8, born: &Arc<AtomicUsize>, retired: &Arc<AtomicUsize>) -> Self {
            born.fetch_add(1, Ordering::Relaxed);
            Self {
                value,
                born: Arc::clone(born),
                retired: Arc::clone(retired),
            }
        }
    }
    impl RopeElem for Tracked {
        const FRESH_LEAF: usize = 16;
        fn same(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }
    impl ObservedRopeElem for Tracked {
        fn clone_observed(&self, p: &mut impl StructuralProgress) -> Result<Self> {
            visit(p)?;
            Ok(Self::new(self.value, &self.born, &self.retired))
        }
        fn same_observed(&self, other: &Self, p: &mut impl StructuralProgress) -> Result<bool> {
            visit(p)?;
            Ok(self.value == other.value)
        }
        fn retire_observed(self, p: &mut impl StructuralProgress) {
            p.retirement_poll();
            self.retired.fetch_add(1, Ordering::Relaxed);
        }
    }

    #[test]
    fn observed_mid_copy_refusal_retires_partial_values_even_after_sticky_stop() {
        let born = Arc::new(AtomicUsize::new(0));
        let retired = Arc::new(AtomicUsize::new(0));
        let mut p = Progress::default();
        let values = (0..16).map(|n| Tracked::new(n, &born, &retired)).collect();
        let original = Rope::dense_observed(values, &mut p).unwrap();
        let replacement = Tracked::new(99, &born, &retired);
        p.limit = Some(p.work + 26);
        assert!(matches!(
            original.set_observed(7, replacement, &mut p),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert!(p.stopped);
        original.retire_observed(&mut p);
        assert_eq!(
            born.load(Ordering::Relaxed),
            retired.load(Ordering::Relaxed),
            "no implicit drop of an owned element, including the partial copy"
        );
        assert!(p.retirement_polls >= born.load(Ordering::Relaxed));
    }

    #[test]
    fn observed_shared_dag_visit_and_copy_only_stop_use_one_control() {
        let mut p = Progress::default();
        let unit = Rope::dense_observed(vec![Some(1u8), None], &mut p).unwrap();
        let repeats = unit.repeat_observed(1 << 40, &mut p).unwrap();
        let mut visits = 0;
        repeats
            .try_for_each_stored_observed(&mut p, |_, _| {
                visits += 1;
                Ok(())
            })
            .unwrap();
        assert_eq!(visits, 2);
        p.copy_limit = Some(p.copies);
        assert!(matches!(
            unit.set_observed(0, Some(2), &mut p),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert!(
            p.stopped,
            "work was available; new physical copy was refused"
        );
        repeats.retire_observed(&mut p);
        unit.retire_observed(&mut p);
    }
}
