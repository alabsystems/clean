// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pointer roots: where each value of one function takes its address from
//! (Trust design 2026-10-02, "C1: the thread model", §3.3).
//!
//! This is the root analysis Trust's effect-conservation census (D28) used to
//! compute privately, lifted here so the census and ty's thread model read one
//! analysis. Two things are added for the thread model: a root names the
//! globals and the allocations it may address, and each allocation carries an
//! escape bit.
//!
//! # The lattice
//!
//! Per value, `unset < {Arg(i), Global(G), Local(A)} < Indirect`, with
//! `Global(G) ≤ Global(G')` when `G ⊆ G'` and `Local(A) ≤ Local(A')` when
//! `A ⊆ A'`. Two different classes, and two different parameters, join to
//! `Indirect`. [`pointer_roots`] computes the least fixpoint over every stored
//! block (dead ones included) of these rules:
//!
//! | Definition | Root |
//! |---|---|
//! | entry-block parameter `i` | `Arg(i)`, joined with any edge into the entry |
//! | any other block parameter | the join of the arguments every edge into its block passes (every edge [`Inst::successor_edges`] lists) |
//! | a parameter of a block an edge enters with a different number of arguments | `Indirect` |
//! | `Alloca` / `HeapAlloc` | `Local({itself})` |
//! | `GlobalAddr g` | `Global({g})` |
//! | `GEP`, `Copy`, `Cast`, `Borrow`, `BorrowMut`, `PtrData`, `PtrFromParts` | the root of the base / operand / pointer / data |
//! | `ExtractField` | `Arg(i)` from an `Arg(i)` aggregate (a field of a by-value parameter), else `Indirect` |
//! | `Select` | the join of both arms |
//! | every other first result, and every later result | `Indirect` (a loaded pointer, a call result, a constant, ...) |
//!
//! An operand no instruction or parameter defines is `Indirect`. A value the
//! fixpoint leaves unset is joined as nothing, and [`PointerRoots::root`]
//! answers `Indirect` for it.
//!
//! # Precondition
//!
//! The roots are claimed for a function the validator accepts: block ids and
//! value definitions are unique, every edge passes as many arguments as its
//! target has parameters (an unwind edge passes none, so a landing pad has no
//! parameters), and every use is dominated by its definition. On such a
//! function a value left unset never holds a value at run time: an execution
//! enters a block only through an edge whose arguments it has already
//! computed, and computes a derived value only after its operands, so by
//! induction every value it computes has a root.
//!
//! The analysis is total on any function and reads a malformed shape at least
//! as high as any resolution of it: an edge whose argument count is not its
//! target's parameter count makes those parameters `Indirect` (rule above), a
//! repeated block id binds an edge to every block that carries it, a repeated
//! definition joins the roots of both, and a repeated entry-parameter id joins
//! `Arg(i)` with `Arg(j)` to `Indirect`. A use that its definition does not
//! dominate may read a value no definition set; nothing is claimed for it.
//!
//! # What a root licenses
//!
//! A root over-approximates: `Indirect` may be any address. A consumer may rely
//! on `Arg(i)` (derived from entry parameter `i` only), `Global(G)` (from the
//! address of a global in `G` only) and `Local(A)` (from an allocation of this
//! function in `A` only), and on nothing else. No type fact is read: no `&mut`
//! exclusivity, no `Freeze`.
//!
//! # Escape
//!
//! An allocation (the result of an `Alloca` or a `HeapAlloc`) is PRIVATE when
//! every use of it in the function is as the address of a `Load` or of a
//! `Store`, never as the value a `Store` writes. That is mem2reg's escape rule
//! for a scalar alloca ([`crate::mem2reg`]), applied to every allocation,
//! counted ones and heap ones included, and with no exception for a call
//! argument. mem2reg's fixed-count integer-array subset also admits
//! constant-offset `GEP`s and pointer `Copy`s of the allocation; here those are
//! escapes, which only makes fewer allocations private. Uses are read through
//! the canonical operand walk ([`Inst::visit_value_operands`]) over every
//! stored instruction, dead ones included. No other code, and so no other
//! thread, can reach a private allocation.
//!
//! # Against the census's private copy
//!
//! On a validated function whose edges are `Br`, `CondBr`, `Switch` and
//! `Invoke` only, with no edge into its entry, every operand defined, and no
//! later result of an instruction flowing into a join, the projection of these
//! roots onto the census's four classes (`Arg(i)`, `Global`, `Local`,
//! `Indirect`) is exactly the census's. Elsewhere they differ by four
//! corrections, each a place the census was optimistic: it omitted the normal
//! edges of `AssertInvoke`, `DropInvoke` and `InvokeIndirect`; it kept an
//! entry parameter at `Arg(i)` whatever an edge into the entry passed; and it
//! joined an undefined operand, or an instruction's later result, as nothing,
//! so a block parameter fed by an allocation and by a call's second result read
//! `Local`.
//!
//! On a function the validator rejects they also differ, not always in one
//! direction:
//! * an edge with the wrong number of arguments (an unwind edge into a block
//!   with parameters, say): the census bound a prefix and left the rest unset,
//!   joined as nothing; here each of those parameters is `Indirect`;
//! * a repeated entry-parameter id: the census kept `Arg` of the last
//!   position; here the positions join to `Indirect`;
//! * a repeated block id: the census bound an edge only to the last block
//!   that carries the id, so another such block's parameters read `Indirect`
//!   there, yet joined as nothing into what they flow to; here every such
//!   block is bound, and its parameters read the arguments' root. Likewise
//!   every block carrying the entry id takes `Arg(i)`, where the census gave
//!   it only to the first.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::Function;
use crate::inst::Inst;
use crate::value::{BlockId, GlobalId, ValueId};

/// Where a value takes its address from (see the module docs).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PointerRoot {
    /// Derived from entry-block parameter `i` only.
    Arg(u32),
    /// The address of one of these module globals, and of nothing else.
    Global(BTreeSet<GlobalId>),
    /// One of these allocations of the function itself (`Alloca` / `HeapAlloc`
    /// results), and nothing else.
    Local(BTreeSet<ValueId>),
    /// Any address.
    Indirect,
}

impl PointerRoot {
    /// The least upper bound of `self` and `other`.
    #[must_use]
    pub fn join(&self, other: &PointerRoot) -> PointerRoot {
        match (self, other) {
            (PointerRoot::Arg(left), PointerRoot::Arg(right)) if left == right => {
                PointerRoot::Arg(*left)
            }
            (PointerRoot::Global(left), PointerRoot::Global(right)) => {
                PointerRoot::Global(left.union(right).copied().collect())
            }
            (PointerRoot::Local(left), PointerRoot::Local(right)) => {
                PointerRoot::Local(left.union(right).copied().collect())
            }
            _ => PointerRoot::Indirect,
        }
    }
}

static INDIRECT: PointerRoot = PointerRoot::Indirect;

/// The roots of one function's values and the escape bits of its allocations,
/// from [`pointer_roots`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PointerRoots {
    roots: HashMap<ValueId, PointerRoot>,
    /// Every allocation of the function, and whether it escapes.
    sites: BTreeMap<ValueId, bool>,
}

impl PointerRoots {
    /// `value`'s root. `Indirect` for a value the function does not define and
    /// for one the fixpoint left unset.
    #[must_use]
    pub fn root(&self, value: ValueId) -> &PointerRoot {
        self.roots.get(&value).unwrap_or(&INDIRECT)
    }

    /// Whether the allocation `site` escapes; `None` when `site` is not the
    /// result of an `Alloca` or a `HeapAlloc` of the function.
    #[must_use]
    pub fn escapes(&self, site: ValueId) -> Option<bool> {
        self.sites.get(&site).copied()
    }

    /// Whether every address `pointer` may hold is a private allocation, so no
    /// other activation or thread can reach what an access through it touches.
    #[must_use]
    pub fn is_private(&self, pointer: ValueId) -> bool {
        match self.root(pointer) {
            PointerRoot::Local(sites) => sites
                .iter()
                .all(|site| self.sites.get(site) == Some(&false)),
            PointerRoot::Arg(_) | PointerRoot::Global(_) | PointerRoot::Indirect => false,
        }
    }
}

/// A definition whose root the fixpoint recomputes when an input changes.
#[derive(Debug, Clone, Copy)]
enum Definition {
    /// A block parameter: the join of its incoming arguments.
    Param(ValueId),
    /// The first result of the instruction at `(block, index)`, derived from
    /// its operands.
    Derived { block: usize, index: usize },
}

/// How an instruction's first result takes its root from its operands.
#[derive(Debug, Clone, Copy)]
enum Derivation {
    /// The operand's root (`GEP`'s base, `Copy`, `Cast`, `Borrow`,
    /// `BorrowMut`, `PtrData`, `PtrFromParts`' data).
    Same(ValueId),
    /// A field of the aggregate: a parameter's root survives, any other root
    /// is `Indirect` (`ExtractField`).
    Field(ValueId),
    /// The join of two operands (`Select`).
    Join(ValueId, ValueId),
}

impl Derivation {
    fn of(inst: &Inst) -> Option<Derivation> {
        match inst {
            Inst::GEP { base: value, .. }
            | Inst::Copy { operand: value, .. }
            | Inst::Cast { operand: value, .. }
            | Inst::Borrow { ptr: value }
            | Inst::BorrowMut { ptr: value }
            | Inst::PtrData { ptr: value, .. }
            | Inst::PtrFromParts { data: value, .. } => Some(Derivation::Same(*value)),
            Inst::ExtractField { aggregate, .. } => Some(Derivation::Field(*aggregate)),
            Inst::Select {
                then_val, else_val, ..
            } => Some(Derivation::Join(*then_val, *else_val)),
            _ => None,
        }
    }

    fn operands(self) -> impl Iterator<Item = ValueId> {
        let (first, second) = match self {
            Derivation::Same(value) | Derivation::Field(value) => (value, None),
            Derivation::Join(left, right) => (left, Some(right)),
        };
        std::iter::once(first).chain(second)
    }

    /// The root from the operands' current roots; `None` while every input is
    /// unset.
    fn apply(self, roots: &HashMap<ValueId, PointerRoot>) -> Option<PointerRoot> {
        match self {
            Derivation::Same(value) => roots.get(&value).cloned(),
            Derivation::Field(aggregate) => roots.get(&aggregate).map(|root| match root {
                PointerRoot::Arg(index) => PointerRoot::Arg(*index),
                PointerRoot::Global(_) | PointerRoot::Local(_) | PointerRoot::Indirect => {
                    PointerRoot::Indirect
                }
            }),
            Derivation::Join(left, right) => match (roots.get(&left), roots.get(&right)) {
                (Some(left), Some(right)) => Some(left.join(right)),
                (Some(root), None) | (None, Some(root)) => Some(root.clone()),
                (None, None) => None,
            },
        }
    }
}

/// Join `root` into `value`'s root; whether it changed.
fn raise(roots: &mut HashMap<ValueId, PointerRoot>, value: ValueId, root: PointerRoot) -> bool {
    match roots.get_mut(&value) {
        Some(old) => {
            let new = old.join(&root);
            let changed = *old != new;
            *old = new;
            changed
        }
        None => {
            roots.insert(value, root);
            true
        }
    }
}

/// The pointer roots of every value of `function`, and the escape bit of every
/// allocation (see the module docs).
#[must_use]
pub fn pointer_roots(function: &Function) -> PointerRoots {
    let mut roots: HashMap<ValueId, PointerRoot> = HashMap::new();
    let mut sites: BTreeMap<ValueId, bool> = BTreeMap::new();

    // Every defined value, and the blocks that carry each id (a repeated id
    // binds an edge to every block that carries it).
    let mut defined: BTreeSet<ValueId> = BTreeSet::new();
    let mut blocks_of: HashMap<BlockId, Vec<usize>> = HashMap::new();
    for (position, block) in function.blocks.iter().enumerate() {
        blocks_of.entry(block.id).or_default().push(position);
        defined.extend(block.params.iter().map(|(value, _)| *value));
        for node in &block.body {
            defined.extend(node.results.iter().copied());
        }
    }

    // The fixed roots; each derived definition with its inputs; each block
    // parameter with its incoming arguments.
    let mut incoming: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
    let mut users: HashMap<ValueId, Vec<Definition>> = HashMap::new();
    let mut pending: Vec<Definition> = Vec::new();
    for block in function
        .blocks
        .iter()
        .filter(|block| block.id == function.entry)
    {
        for (index, (value, _)) in block.params.iter().enumerate() {
            let root = u32::try_from(index).map_or(PointerRoot::Indirect, PointerRoot::Arg);
            raise(&mut roots, *value, root);
        }
    }
    for (block_position, block) in function.blocks.iter().enumerate() {
        for (index, node) in block.body.iter().enumerate() {
            for edge in node.inst.successor_edges() {
                for &target in blocks_of.get(&edge.target).map_or(&[][..], Vec::as_slice) {
                    let params = &function.blocks[target].params;
                    if params.len() != edge.args.len() {
                        // Which argument reaches which parameter is not
                        // stated (an unwind edge into a block with
                        // parameters is one such edge): each may be any
                        // address.
                        for (param, _) in params {
                            raise(&mut roots, *param, PointerRoot::Indirect);
                        }
                        continue;
                    }
                    for ((param, _), argument) in params.iter().zip(edge.args) {
                        incoming.entry(*param).or_default().push(*argument);
                        users
                            .entry(*argument)
                            .or_default()
                            .push(Definition::Param(*param));
                        pending.push(Definition::Param(*param));
                    }
                }
            }
            let Some((&first, later)) = node.results.split_first() else {
                continue;
            };
            for value in later {
                raise(&mut roots, *value, PointerRoot::Indirect);
            }
            match &node.inst {
                Inst::Alloca { .. } | Inst::HeapAlloc { .. } => {
                    sites.insert(first, false);
                    raise(
                        &mut roots,
                        first,
                        PointerRoot::Local(BTreeSet::from([first])),
                    );
                }
                Inst::GlobalAddr { global } => {
                    raise(
                        &mut roots,
                        first,
                        PointerRoot::Global(BTreeSet::from([*global])),
                    );
                }
                inst => match Derivation::of(inst) {
                    Some(derivation) => {
                        let user = Definition::Derived {
                            block: block_position,
                            index,
                        };
                        for operand in derivation.operands() {
                            users.entry(operand).or_default().push(user);
                        }
                        pending.push(user);
                    }
                    None => {
                        raise(&mut roots, first, PointerRoot::Indirect);
                    }
                },
            }
        }
    }
    // An input nothing defines may be any address.
    for value in users.keys() {
        if !defined.contains(value) {
            raise(&mut roots, *value, PointerRoot::Indirect);
        }
    }

    // The least fixpoint: a definition is recomputed whenever an input
    // changes. Roots only rise in a finite lattice, so it terminates.
    while let Some(definition) = pending.pop() {
        let (value, root) = match definition {
            Definition::Param(param) => {
                let root = incoming
                    .get(&param)
                    .into_iter()
                    .flatten()
                    .filter_map(|argument| roots.get(argument))
                    .fold(None::<PointerRoot>, |joined, root| {
                        Some(joined.map_or_else(|| root.clone(), |joined| joined.join(root)))
                    });
                (param, root)
            }
            Definition::Derived { block, index } => {
                let node = &function.blocks[block].body[index];
                let Some(&value) = node.results.first() else {
                    continue;
                };
                let root =
                    Derivation::of(&node.inst).and_then(|derivation| derivation.apply(&roots));
                (value, root)
            }
        };
        if let Some(root) = root
            && raise(&mut roots, value, root)
        {
            pending.extend(users.get(&value).into_iter().flatten().copied());
        }
    }

    // Escape: every use but as the address of a `Load` or a `Store`.
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        let mut escape = |value: ValueId| {
            if let Some(escapes) = sites.get_mut(&value) {
                *escapes = true;
            }
        };
        match &node.inst {
            // Its one operand is the address it reads.
            Inst::Load { .. } => {}
            // The address it writes is not an escape; the value it writes is.
            Inst::Store { value, .. } => escape(*value),
            inst => inst.visit_value_operands(escape),
        }
    }

    PointerRoots { roots, sites }
}
