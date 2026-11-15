// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lossless, explicitly versioned Clean expression DAG transport.
//!
//! This is a carrier, never proof authority. The legacy v1 codec is unchanged.
//! Nodes are emitted in deterministic first-encounter postorder, with structural
//! interning of shallow records. References are typed, backwards-only indices
//! into one arena of Name, Level and Expr nodes. No recursive Expr equality or
//! hashing participates. Decode requires exact field spellings and structural
//! uniqueness, then checks rooted first-child postorder directly on node IDs.
//! This establishes canonical order and full reachability without re-encoding
//! or expanding the reconstructed kernel graph.
//!
//! Encoder scratch records have a separate aggregate bound equal to the carrier
//! byte cap. Committed records and pending scratch therefore use at most twice
//! that cap in payload storage (plus bounded node/reference indexes). Keeping
//! those budgets separate permits an unshared equal node to be compared with an
//! existing record even when the final canonical carrier exactly fills its cap.
//!
//! Unlike Clean's flat database, this preserves every binder attribute, name
//! component, literal representation, metadata entry and expression mode.

use clean_kernel::{Expr, Level, Name};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[path = "clean_expr_dag/read.rs"]
mod read;
#[path = "clean_expr_dag/shape.rs"]
mod shape;
#[cfg(test)]
#[path = "clean_expr_dag/tests.rs"]
mod tests;

/// Hard whole-carrier byte cap; unchanged from the legacy carrier.
pub const CLEAN_EXPR_DAG_V2_MAX_BYTES: usize = 64 * 1024 * 1024;
/// Combined pending and interned record payload storage, excluding node indexes.
pub const CLEAN_EXPR_DAG_V2_MAX_SCRATCH_BYTES: usize = 2 * CLEAN_EXPR_DAG_V2_MAX_BYTES;
/// Aggregate shallow payload bytes processed while encoding input identities.
/// Shared immutable Name components bypass this work through exact memo keys.
pub const CLEAN_EXPR_DAG_V2_MAX_ENCODE_WORK_BYTES: usize = 2 * CLEAN_EXPR_DAG_V2_MAX_BYTES;
/// Aggregate unique Name/Level/Expr records in a carrier. Encoding also limits
/// distinct input identities to this count, bounding its pointer memo and work.
pub const CLEAN_EXPR_DAG_V2_MAX_NODES: usize = 2_000_000;
/// Maximum combined Name/Level/Expr graph depth, with leaves at depth one.
pub const CLEAN_EXPR_DAG_V2_MAX_DEPTH: usize = 4_096;
/// Bounded expanded Level work in existing Clean expression constructors.
///
/// Clean's current Sort/Const metadata hashing traverses Level trees rather
/// than memoizing their DAG. Charge that hidden work *before* construction;
/// compact malicious shared levels must not cause exponential CPU use.
pub const CLEAN_EXPR_DAG_V2_MAX_CONSTRUCTOR_WORK: usize = 2_000_000;

const MAGIC: &[u8; 8] = b"CEXDAG02";
const HEADER: usize = 16;
type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Copy)]
struct Limits {
    bytes: usize,
    nodes: usize,
    depth: usize,
    constructor_work: usize,
}

const LIMITS: Limits = Limits {
    bytes: CLEAN_EXPR_DAG_V2_MAX_BYTES,
    nodes: CLEAN_EXPR_DAG_V2_MAX_NODES,
    depth: CLEAN_EXPR_DAG_V2_MAX_DEPTH,
    constructor_work: CLEAN_EXPR_DAG_V2_MAX_CONSTRUCTOR_WORK,
};

fn require(ok: bool, reason: &str) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(format!("Clean Expr DAG v2: {reason}"))
    }
}

#[derive(Clone, Copy)]
enum Input<'a> {
    Name(&'a Name),
    Level(&'a Level),
    Expr(&'a Expr),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum InputKey {
    Anonymous,
    NameString(usize, usize, usize),
    NameNumber(usize, u64),
    Level(usize),
    Expr(usize),
}

impl Input<'_> {
    fn kind(self) -> u8 {
        match self {
            Self::Name(_) => 0,
            Self::Level(_) => 1,
            Self::Expr(_) => 2,
        }
    }
    fn key(self) -> InputKey {
        match self {
            // Name clones retain these immutable Arc components. Matching all
            // components proves exact value identity without copying or hashing
            // a potentially huge string once per metadata/constant occurrence.
            Self::Name(n) => match n.inner() {
                clean_kernel::name::NameInner::Anon => InputKey::Anonymous,
                clean_kernel::name::NameInner::Str(parent, text) => InputKey::NameString(
                    Arc::as_ptr(parent) as usize,
                    text.as_ptr() as usize,
                    text.len(),
                ),
                clean_kernel::name::NameInner::Num(parent, n) => {
                    InputKey::NameNumber(Arc::as_ptr(parent) as usize, *n)
                }
            },
            Self::Level(l) => InputKey::Level(l as *const Level as usize),
            Self::Expr(e) => InputKey::Expr(e as *const Expr as usize),
        }
    }
}

struct Pending<'a> {
    input: Input<'a>,
    bytes: Vec<u8>,
    children: Vec<(usize, Input<'a>)>,
    next: usize,
    depth: usize,
}

/// Encode one exact kernel expression without expanding its shared subgraphs.
pub fn encode_clean_expr_dag_v2(expr: &Expr) -> Result<Vec<u8>> {
    encode(expr, LIMITS)
}

fn encode(expr: &Expr, limits: Limits) -> Result<Vec<u8>> {
    require(limits.bytes >= HEADER, "byte limit exceeded")?;
    require(limits.nodes > 0, "unique node limit exceeded")?;
    require(limits.depth > 0, "graph depth limit exceeded")?;
    let mut memo: HashMap<InputKey, (u32, usize)> = HashMap::new();
    let mut intern: HashMap<Arc<[u8]>, (u32, usize)> = HashMap::new();
    let mut records: Vec<Arc<[u8]>> = Vec::new();
    let mut total = HEADER;
    let first = shape::pending(Input::Expr(expr), limits)?;
    let mut pending_bytes = first.bytes.len();
    let mut processed_bytes = pending_bytes;
    let mut pending = vec![first];
    let root;
    loop {
        require(pending.len() <= limits.depth, "graph depth limit exceeded")?;
        let frame = pending.last_mut().expect("pending root");
        if let Some(&(offset, child)) = frame.children.get(frame.next) {
            if let Some(&(index, depth)) = memo.get(&child.key()) {
                frame.bytes[offset..offset + 4].copy_from_slice(&index.to_le_bytes());
                frame.depth = frame.depth.max(depth + 1);
                frame.next += 1;
            } else {
                require(pending.len() < limits.depth, "graph depth limit exceeded")?;
                require(
                    memo.len() + pending.len() < limits.nodes,
                    "input identity limit exceeded",
                )?;
                let available = limits.bytes.saturating_sub(pending_bytes).min(
                    limits
                        .bytes
                        .saturating_mul(2)
                        .saturating_sub(processed_bytes),
                );
                let child = shape::pending(
                    child,
                    Limits {
                        bytes: available,
                        ..limits
                    },
                )?;
                pending_bytes += child.bytes.len();
                processed_bytes += child.bytes.len();
                pending.push(child);
            }
            continue;
        }
        let frame = pending.pop().expect("completed frame");
        pending_bytes -= frame.bytes.len();
        require(frame.depth <= limits.depth, "graph depth limit exceeded")?;
        let found = if let Some(&entry) = intern.get(frame.bytes.as_slice()) {
            entry
        } else {
            require(records.len() < limits.nodes, "unique node limit exceeded")?;
            total = total
                .checked_add(4)
                .and_then(|n| n.checked_add(frame.bytes.len()))
                .ok_or("Clean Expr DAG v2: byte count overflow")?;
            require(total <= limits.bytes, "byte limit exceeded")?;
            let index = u32::try_from(records.len())
                .map_err(|_| "Clean Expr DAG v2: node index overflow")?;
            let record: Arc<[u8]> = frame.bytes.into();
            records.push(record.clone());
            intern.insert(record, (index, frame.depth));
            (index, frame.depth)
        };
        // Never evict shared inputs and accidentally expand their DAG as a tree.
        require(memo.len() < limits.nodes, "input identity limit exceeded")?;
        memo.insert(frame.input.key(), found);
        if pending.is_empty() {
            root = found.0;
            break;
        }
    }
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(MAGIC);
    bytes.extend_from_slice(&(records.len() as u32).to_le_bytes());
    bytes.extend_from_slice(&root.to_le_bytes());
    for record in records {
        bytes.extend_from_slice(&(record.len() as u32).to_le_bytes());
        bytes.extend_from_slice(&record);
    }
    Ok(bytes)
}

enum Output {
    Name(Name),
    Level(Arc<Level>),
    Expr(Arc<Expr>),
}

struct Decoded {
    value: Output,
    depth: usize,
    level_work: usize,
    references: std::ops::Range<usize>,
}

/// Decode a bounded, exact canonical DAG carrier; this does not check a proof.
pub fn decode_clean_expr_dag_v2(bytes: &[u8]) -> Result<Expr> {
    decode(bytes, LIMITS)
}

fn decode(bytes: &[u8], limits: Limits) -> Result<Expr> {
    require(bytes.len() <= limits.bytes, "byte limit exceeded")?;
    let mut input = read::Reader::new(bytes);
    require(input.take(8)? == MAGIC, "wrong carrier magic/version")?;
    let count = input.u32()? as usize;
    let root = input.u32()? as usize;
    require(
        count > 0 && count <= limits.nodes,
        "unique node limit exceeded",
    )?;
    // A record has a length word and at least its two type/tag bytes. Check the
    // entire count before allocating the table, even for a tiny malicious input.
    require(count <= input.remaining() / 6, "truncated node table")?;
    require(root == count - 1, "root is not the final expression node")?;
    let mut nodes = Vec::with_capacity(count);
    let mut seen = HashSet::with_capacity(count);
    let mut constructor_work = 0usize;
    let mut edges = Vec::new();
    for _ in 0..count {
        let length = input.u32()? as usize;
        let record = input.take(length)?;
        require(seen.insert(record), "duplicate structural node")?;
        nodes.push(read::node(
            record,
            &nodes,
            limits,
            &mut constructor_work,
            &mut edges,
        )?);
    }
    require(input.remaining() == 0, "trailing carrier bytes")?;
    let Output::Expr(expr) = &nodes[root].value else {
        return Err("Clean Expr DAG v2: root is not an Expr".into());
    };
    canonical_order(&nodes, &edges, root)?;
    Ok(expr.as_ref().clone())
}

fn canonical_order(nodes: &[Decoded], edges: &[u32], root: usize) -> Result<()> {
    // Typed earlier-only references already exclude cycles. Equal shallow
    // records were rejected during read; by induction these are exactly unique
    // structural nodes. Their sole canonical numbering is first-encounter DFS
    // postorder. This O(nodes + edges) check needs no Expr hash/equality/codec.
    let mut visited = vec![false; nodes.len()];
    let mut stack = vec![(root, nodes[root].references.start)];
    let mut expected = 0usize;
    while let Some((node, cursor)) = stack.last_mut() {
        if *cursor < nodes[*node].references.end {
            let child = edges[*cursor] as usize;
            *cursor += 1;
            if !visited[child] {
                stack.push((child, nodes[child].references.start));
            }
        } else {
            require(*node == expected, "noncanonical or unreachable DAG records")?;
            visited[*node] = true;
            expected += 1;
            stack.pop();
        }
    }
    require(
        expected == nodes.len(),
        "noncanonical or unreachable DAG records",
    )
}
