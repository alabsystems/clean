// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Borrowed census of explicit IR dependencies of one actual function, and the
//! spawn census's reachability engine, whose trust-ir walk shares this
//! census's module lookups and exhaustive instruction and constant matches.
//!
//! [`inspect_function_dependencies`] does not project, renumber, validate,
//! interpret, or certify a module. In particular, an empty refusal list is NOT
//! source completeness, semantic closure, Rust refinement, or a code-generation
//! license. A RESOLVED drop (amendment D: a drop-glue row names its glue) is a
//! call edge to that glue; the destructor an UNRESOLVED `Inst::Drop` runs
//! names no function, so the census cannot follow it and REFUSES it
//! (`ImplicitDestructor`) rather than dropping the dependency silently. The other runtime services implicit in instructions
//! (a failed `Assert`'s panic path, an allocator, a reference-count runtime) and
//! proof/producer claims require separate checks. The original module (including
//! all claims, imports, layouts and unused rows) stays borrowed and unchanged.
//! Every stored block of a reached function is scanned, even unreachable blocks
//! and instructions after a terminator.
//! [`inspect_defined_function_dependencies`] seeds every stored definition in
//! one traversal, with the same refusals and no new authority. Its explicit
//! root inventory is separate from the unchanged single-root census.
//!
//! # The reachability engine (spawn census, design 2026-09-29 §5)
//!
//! [`ReachGraph`] is rustc-free and IR-agnostic: an adapter feeds it FACTS —
//! labelled edges `(from, to, class, site, via_drop)`, UNKNOWN sinks with a
//! reason, and the indirect-call facts of [`crate::analysis`] (pool members,
//! invoking sites, hand-offs, LAUNDER, LIFETIME-ERASE, upcasts), one lane per
//! graph. It is built for two adapters: trustc's MIR adapter (plan step P2,
//! not built yet: nothing in trustc calls this engine today) and the trust-ir
//! adapter, [`inspect_module_reachability`] (its trustc caller is step P4).
//! [`ReachGraph::solve`] closes the pools, derives the APPROX edges (pools and
//! rule H), and runs four backward reachabilities from the seeds, each
//! admitting more edge classes than the one before:
//!
//! | Verdict | A path to a seed (or, for UNKNOWN, a sink) uses |
//! |---|---|
//! | [`Verdict::Spawns`] | RUN only: the only verdict that claims a spawn |
//! | [`Verdict::Escapes`] | RUN, CREATE, READ |
//! | [`Verdict::Indirect`] | RUN, CREATE, READ, APPROX |
//! | [`Verdict::Unknown`] | any of those, to a seed or an UNKNOWN sink |
//! | [`Verdict::Quiet`] | none: the only verdict that does not refuse |
//!
//! PARAM edges are recorded but admitted by no verdict (R1: reach only through
//! the definition's own type parameters is refused by the supplying crate).
//!
//! The labelling IS a certificate. [`check_reach_certificate`] re-verifies it
//! against the expanded graph in O(V + E), plus an ordered map for the
//! per-definition join, without the solver's breadth-first search, and
//! `solve` always runs it: a rejected certificate, or a malformed fact, turns
//! EVERY node UNKNOWN and claims no spawn. The checker checks the labelling,
//! not the graph. It takes the expanded graph as given: a fact an adapter
//! never emitted, and an APPROX edge the engine failed to derive (pool
//! closure, rule H, unclosed pools), are invisible to it. Those derivations
//! are trusted code, and the checker shares `EdgeClass::cap`, the base labels
//! and the per-definition join with the solver; the census's TCB row must
//! name all of them.
//!
//! The derived APPROX edges are stored through HUBS ([`ReachNodeKind::Hub`]):
//! each derivation fact (an invoke, a hand-off round) is an edge from its node
//! to the hub of its target list, and each hub has an edge to every target,
//! so a pool that thousands of sites invoke costs one list, not sites ×
//! members edges. The certificate labels and checks that compressed graph, in
//! which a hub's label is what its targets give an APPROX edge, so every
//! other node's label is the uncompressed graph's. The search passes a hub at
//! no cost and scans its facts in derivation order, so distances, parents and
//! witnesses are the uncompressed search's as well; witnesses, spawn sites
//! and thread closures name the logical edges, never a hub
//! ([`ExpandedReachGraph::derived_edge_scan`]). A test-only copy of the
//! uncompressed derivation checks all of this on random graphs
//! (`compressed_derivation_tests`).

mod observed_graph;
mod observed_thread_closure;
pub use observed_graph::inspect_native_module_reachability_observed;

use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::{Hash, Hasher};

use crate::analysis::{
    CarriedKey, ClosedPools, FnShape, IndirectCallUniverse, InvokedKeySummaries, InvokedKeys,
    PoolHandoff, PoolInvoke, PoolKey, PoolMember, PrincipalKey, StaticFunctionPointerAnalysis,
    carried_keys, cast_launders, fn_pool_shape,
};
use crate::inst::{AllocOrigin, CastOp, SwitchCase};
use crate::value::{
    BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, GlobalId, PredId, RecordId, StructId, TyId,
    UnivId, ValueId,
};
use crate::{
    CallingConv, Constant, FatPtrKind, Function, Inst, Module, ModuleFunctionCatalog,
    NominalTypeReachability, Pred, Ty, Universe,
};
use std::sync::atomic::{AtomicU64, Ordering};

/// An original module-local identity, never a dense replacement ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DependencyNode {
    Function(FuncId),
    Global(GlobalId),
    Type(TyId),
    FunctionType(FuncTyId),
    Struct(StructId),
    Enum(EnumId),
    Record(RecordId),
    ClosureType(ClosureTyId),
    Predicate(PredId),
    Universe(UnivId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DependencySite {
    Module,
    Root,
    Definition(DependencyNode),
    Instruction {
        function: FuncId,
        block: BlockId,
        index: usize,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DependencyEdge {
    pub site: DependencySite,
    pub target: DependencyNode,
}

/// Why a dependency is refused, and the reason an UNKNOWN sink carries. Each
/// variant names who emits it: the dependency census
/// ([`inspect_function_dependencies`]), the trust-ir walk
/// ([`inspect_module_reachability`], directly or through its
/// [`DeclClassifier`]), the MIR adapter (design 2026-09-29 §5.3, plan step
/// P2, not built yet), or the engine itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DependencyRefusalKind {
    /// Census and trust-ir walk: an id or symbol target the module lacks.
    Missing(DependencyNode),
    /// Census and trust-ir walk: an id two definitions share.
    Ambiguous(DependencyNode),
    /// Census and trust-ir walk: a reached function with no stored body.
    BodylessFunction(FuncId),
    /// Census and trust-ir walk: a global whose contents are not in the module.
    MissingGlobalInitializer(GlobalId),
    /// Census and trust-ir walk: a `SymbolAddr` naming nothing in the module.
    UnresolvedSymbol(String),
    /// Census and trust-ir walk: a `SymbolAddr` two definitions share.
    AmbiguousSymbol(String),
    /// Census: an indirect call with no exact target (the trust-ir walk pools
    /// it instead).
    IndirectCall,
    /// Census and trust-ir walk: an exact indirect target whose signature or
    /// convention disagrees with the call.
    IndirectSignatureMismatch,
    /// Census and trust-ir walk: a `DialectOp`.
    OpaqueDialectOperation,
    /// Census: a type with no inspectable structure.
    OpaqueType,
    /// Census and trust-ir walk: module-level assembly.
    GlobalAssembly,
    /// Census and trust-ir walk: a block id two blocks share.
    AmbiguousBlock(BlockId),
    /// Census and trust-ir walk: an entry block the body does not store.
    MissingEntryBlock(BlockId),
    /// Census and trust-ir walk: a global at a position no `GlobalId` names.
    GlobalTableTooLarge,
    /// Census and trust-ir walk: an UNRESOLVED `Inst::Drop` / `DropInvoke`
    /// runs this type's destructor, which no function identity in the module
    /// names (no drop-glue row states it; amendment D).
    ImplicitDestructor(Ty),
    /// Trust-ir walk ([`FunctionClass::WalkDropsElided`]): the producer elided
    /// this body's drops, so its destructors are not in it.
    ElidedDrops,
    /// Trust-ir classifier: a bodyless havoc declaration standing for a call
    /// the producer did not resolve and that is not through the caller's own
    /// type parameters (including every `dyn` dispatch today).
    HavocDeclaration,
    /// Trust-ir classifier, and the MIR adapter for a MIR-less std item:
    /// another crate's Rust code with no body here.
    UnresolvedExtern,
    /// MIR adapter: an instance nested deeper than `recursion_limit`.
    Widened,
    /// MIR adapter: inline assembly.
    InlineAsm,
    /// MIR adapter: an async-drop shim.
    AsyncDropShim,
    /// MIR adapter: a `coroutine_clone` shim.
    CoroutineClone,
    /// MIR adapter: rustc's instance resolver returned `Err`.
    ResolutionError,
    /// MIR adapter (self-audit check 2): a `mentioned_items()` entry of the
    /// codegen body that no fact covers.
    UncoveredMention,
    /// Engine: a `dyn` principal whose runtime types are not all recorded (a
    /// fact names it, or an upcast reaches it, with no recorded member).
    OpenPrincipal,
    /// Engine: an indirect call (or a rule H hand-off) whose pool may hold a
    /// callable minted by code the census did not enumerate: the graph has
    /// an UNKNOWN sink or an open principal ([`ClosedPools::unclosed`]).
    UnclosedPool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DependencyRefusal {
    pub site: DependencySite,
    pub kind: DependencyRefusalKind,
}

/// Diagnostic data bound by borrowing to the exact original module.
#[derive(Debug)]
pub struct FunctionDependencyCensus<'module> {
    module: &'module Module,
    root: FuncId,
    nodes: BTreeSet<DependencyNode>,
    edges: Vec<DependencyEdge>,
    refusals: Vec<DependencyRefusal>,
}

impl<'module> FunctionDependencyCensus<'module> {
    pub fn module(&self) -> &'module Module {
        self.module
    }

    pub fn root(&self) -> FuncId {
        self.root
    }

    /// All referenced identities, INCLUDING missing or ambiguous referents.
    /// Consult refusals; this set is not a set of validated definitions.
    pub fn nodes(&self) -> &BTreeSet<DependencyNode> {
        &self.nodes
    }

    /// Every observed edge, including repeats, in deterministic discovery order.
    /// Nested constant paths and relocation addends stay in the borrowed input;
    /// these coarse sites identify the containing instruction or definition.
    pub fn edges(&self) -> &[DependencyEdge] {
        &self.edges
    }

    pub fn refusals(&self) -> &[DependencyRefusal] {
        &self.refusals
    }
}

/// Inspect references without converting a partial source artifact into a
/// smaller supposedly complete program. Each table node expands once, so
/// recursive types, functions and global initializers terminate. Inline types
/// and constants use the shared stack-safe visitors. No cutoff silently drops
/// a dependency. Malformed IDs never select an arbitrary first declaration.
pub fn inspect_function_dependencies(
    module: &Module,
    root: FuncId,
) -> FunctionDependencyCensus<'_> {
    let mut walker = Walker::new(module, root);
    walker.edge(DependencySite::Root, DependencyNode::Function(root));
    while let Some(node) = walker.pending.pop_front() {
        walker.expand(node);
    }
    walker.census
}

/// Dependencies of every stored definition, using one borrowed traversal.
///
/// This is diagnostic data, not a projection, completeness claim, semantic
/// proof or code-generation license. Bodyless rows are not roots, but remain
/// dependencies (and named refusals) when a stored definition references them.
#[derive(Debug)]
pub struct DefinedFunctionDependencyCensus<'module> {
    module: &'module Module,
    roots: Vec<FuncId>,
    nodes: BTreeSet<DependencyNode>,
    edges: Vec<DependencyEdge>,
    refusals: Vec<DependencyRefusal>,
}

impl<'module> DefinedFunctionDependencyCensus<'module> {
    pub fn module(&self) -> &'module Module {
        self.module
    }

    pub fn roots(&self) -> &[FuncId] {
        &self.roots
    }

    pub fn nodes(&self) -> &BTreeSet<DependencyNode> {
        &self.nodes
    }

    pub fn edges(&self) -> &[DependencyEdge] {
        &self.edges
    }

    pub fn refusals(&self) -> &[DependencyRefusal] {
        &self.refusals
    }
}

/// Seed every actual stored definition before walking. Shared callees, types
/// and globals expand once, rather than once per root. The original single-root
/// API and its ordered diagnostics are unchanged; this API records its own
/// explicit root inventory and deterministic breadth-first discovery order.
pub fn inspect_defined_function_dependencies(
    module: &Module,
) -> DefinedFunctionDependencyCensus<'_> {
    let roots: Vec<_> = module
        .functions
        .iter()
        .filter(|function| function.has_body())
        .map(|function| function.id)
        .collect();
    let Some(&first) = roots.first() else {
        return DefinedFunctionDependencyCensus {
            module,
            roots,
            nodes: BTreeSet::new(),
            edges: Vec::new(),
            refusals: ModuleIndex::new(module)
                .module_refusals(module)
                .into_iter()
                .map(|kind| DependencyRefusal {
                    site: DependencySite::Module,
                    kind,
                })
                .collect(),
        };
    };
    let mut walker = Walker::new(module, first);
    for &root in &roots {
        walker.edge(DependencySite::Root, DependencyNode::Function(root));
    }
    while let Some(node) = walker.pending.pop_front() {
        walker.expand(node);
    }
    DefinedFunctionDependencyCensus {
        module,
        roots,
        nodes: walker.census.nodes,
        edges: walker.census.edges,
        refusals: walker.census.refusals,
    }
}

type NamedIndex = BTreeMap<u32, Option<usize>>;

fn named_index(ids: impl Iterator<Item = u32>) -> NamedIndex {
    let mut index = BTreeMap::new();
    for (position, id) in ids.enumerate() {
        index
            .entry(id)
            .and_modify(|entry| *entry = None)
            .or_insert(Some(position));
    }
    index
}

/// Whether an exactly resolved indirect call agrees with its target: the
/// originating constant's signature, the target's declared signature and
/// convention all equal the call's.
fn exact_indirect_target(
    functions: &ModuleFunctionCatalog<'_>,
    resolution: &crate::analysis::StaticFunctionPointerResolution,
    sig: FuncTyId,
    calling_conv: CallingConv,
) -> bool {
    resolution.declared_signature() == sig
        && functions
            .unique(resolution.function())
            .is_some_and(|target| target.ty == sig && target.calling_conv == calling_conv)
}

/// Link-time symbols of a module's functions and globals. A name two
/// definitions share is ambiguous; it never selects either.
struct SymbolTable<'module> {
    symbols: BTreeMap<&'module str, Option<DependencyNode>>,
    /// A global sits at a position no `GlobalId` can name.
    too_large: bool,
}

impl<'module> SymbolTable<'module> {
    fn new(module: &'module Module) -> Self {
        let mut table = Self {
            symbols: BTreeMap::new(),
            too_large: false,
        };
        for function in &module.functions {
            table.insert(&function.name, DependencyNode::Function(function.id));
        }
        for (position, global) in module.globals.iter().enumerate() {
            match u32::try_from(position) {
                Ok(id) => table.insert(&global.name, DependencyNode::Global(GlobalId(id))),
                Err(_) => table.too_large = true,
            }
        }
        table
    }

    fn insert(&mut self, name: &'module str, node: DependencyNode) {
        self.symbols
            .entry(name)
            .and_modify(|entry| *entry = None)
            .or_insert(Some(node));
    }

    fn resolve(&self, symbol: &str) -> Result<DependencyNode, DependencyRefusalKind> {
        match self.symbols.get(symbol).copied() {
            Some(Some(target)) => Ok(target),
            Some(None) => Err(DependencyRefusalKind::AmbiguousSymbol(symbol.to_owned())),
            None => Err(DependencyRefusalKind::UnresolvedSymbol(symbol.to_owned())),
        }
    }
}

/// The module lookups both walks share, so a malformed module is refused the
/// same way by each: function ids (a duplicate id is ambiguous and never
/// selects the first body), link-time symbols, and the module-level refusals.
struct ModuleIndex<'module> {
    functions: ModuleFunctionCatalog<'module>,
    ambiguous_functions: BTreeSet<u32>,
    symbols: SymbolTable<'module>,
    /// The drop-glue table (amendment D): what each drop calls.
    drop_glue: crate::DropGlueIndex,
}

impl<'module> ModuleIndex<'module> {
    fn new(module: &'module Module) -> Self {
        let functions = ModuleFunctionCatalog::new(module);
        Self {
            ambiguous_functions: functions.ambiguous_ids().collect(),
            functions,
            symbols: SymbolTable::new(module),
            drop_glue: module.drop_glue_index(),
        }
    }

    fn function(&self, id: FuncId) -> Result<&'module Function, DependencyRefusalKind> {
        self.functions.unique(id).ok_or_else(|| {
            let node = DependencyNode::Function(id);
            if self.ambiguous_functions.contains(&id.index()) {
                DependencyRefusalKind::Ambiguous(node)
            } else {
                DependencyRefusalKind::Missing(node)
            }
        })
    }

    /// Refusals that hold for the whole module, in a fixed order.
    fn module_refusals(&self, module: &Module) -> Vec<DependencyRefusalKind> {
        let mut refusals = Vec::new();
        if self.symbols.too_large {
            refusals.push(DependencyRefusalKind::GlobalTableTooLarge);
        }
        if !module.global_asm.is_empty() {
            refusals.push(DependencyRefusalKind::GlobalAssembly);
        }
        refusals
    }
}

/// The refusals of a body's shape: no stored body; else a missing entry
/// block, then each repeated block id in block order. Both walks still scan
/// every stored block.
fn body_shape_refusals(function: &Function) -> Vec<DependencyRefusalKind> {
    if function.blocks.is_empty() {
        return vec![DependencyRefusalKind::BodylessFunction(function.id)];
    }
    let mut refusals = Vec::new();
    if !function
        .blocks
        .iter()
        .any(|block| block.id == function.entry)
    {
        refusals.push(DependencyRefusalKind::MissingEntryBlock(function.entry));
    }
    let mut blocks = BTreeSet::new();
    for block in &function.blocks {
        if !blocks.insert(block.id) {
            refusals.push(DependencyRefusalKind::AmbiguousBlock(block.id));
        }
    }
    refusals
}

/// What one constant node names. The ONE exhaustive match over `Constant`
/// that both walks read (beside [`instruction_reach`] over `Inst`), so a new
/// constant form is reviewed once for both. Nested constants are reached by
/// `Constant::visit_constants`, which visits each child once.
enum ConstantReach<'module> {
    /// `FnDef`.
    Function(FuncId),
    /// `Closure`: its body function.
    Closure(FuncId),
    /// `SymbolAddr`: a function or a global, by link name.
    Symbol(&'module str),
    Nothing,
}

fn constant_reach(constant: &Constant) -> ConstantReach<'_> {
    match constant {
        Constant::FnDef(function) => ConstantReach::Function(*function),
        Constant::Closure { func, .. } => ConstantReach::Closure(*func),
        Constant::SymbolAddr { symbol, addend: _ } => ConstantReach::Symbol(symbol),
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::Aggregate(_)
        | Constant::Array(_)
        | Constant::Vector(_)
        | Constant::Sequence(_)
        | Constant::Set(_)
        | Constant::Record(_)
        | Constant::PhantomData
        // Crystal lane (E3b): an unwritten lane names no identity.
        | Constant::Uninit
        // v50: the one element is a child the visitor reaches (once).
        | Constant::Splat { .. }
        // v70: a blob table key names data, never a function or a global.
        | Constant::TensorBlob { .. } => ConstantReach::Nothing,
        Constant::Ext(e) => e.unreachable(),
    }
}

/// A runtime service an instruction runs without naming a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RuntimeService {
    /// A failed `Assert`. TrustIr's semantics make it a trap, but the Rust
    /// program it stands for panics first, which runs the process's panic
    /// hook: a global registry a program can fill with a spawning callable
    /// (design 2026-09-29 §1.2, p04).
    Panic,
    /// `HeapAlloc` from this origin's runtime (`RustHeap` runs the
    /// `#[global_allocator]`, j04).
    Allocate(AllocOrigin),
    /// `Dealloc`; the origin is the pointer's, not stated by the instruction.
    Deallocate,
    /// `Retain` / `Release` / `IsUnique`: the reference-count runtime.
    ReferenceCount,
}

/// What one instruction can run, name or read. The ONE exhaustive match over
/// `Inst` that both the dependency census and the reachability builder read,
/// so a new instruction is reviewed once for both.
enum InstructionReach<'module> {
    /// `Call` / `Invoke`.
    Call(FuncId),
    /// `SeqMap`'s element function.
    SeqMap(FuncId),
    Indirect {
        callee: ValueId,
        sig: FuncTyId,
        calling_conv: CallingConv,
    },
    /// `GlobalAddr`.
    Global(GlobalId),
    /// `Const`, with the type it is stated at.
    Constant(&'module Constant, &'module Ty),
    /// Constructs a callable value without running its body.
    Closure(crate::value::ClosureTyId, FuncId),
    /// `Switch` case constants.
    Cases(&'module [SwitchCase]),
    /// An UNRESOLVED `Drop` / `DropInvoke` (no drop-glue row): runs this
    /// type's destructor, which no function identity in the module names.
    Drop(&'module Ty),
    /// A RESOLVED `Drop` / `DropInvoke` (amendment D, §20): a call of this
    /// glue.
    DropGlue(FuncId),
    /// `DialectOp`.
    Opaque,
    Cast {
        op: CastOp,
        src: &'module Ty,
        dst: &'module Ty,
    },
    Runtime(RuntimeService),
    /// A sited `Assert` / `AssertInvoke` (amendment P): its failure calls
    /// `entry` and passes the address of `global` when the location is a
    /// `Global`, so both are dependencies and neither is a dead declaration.
    PanicSite {
        entry: FuncId,
        global: Option<GlobalId>,
    },
    /// Nothing beyond the types the instruction spells.
    Nothing,
}

fn instruction_reach<'module>(
    inst: &'module Inst,
    drop_glue: &crate::DropGlueIndex,
) -> InstructionReach<'module> {
    match inst {
        Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => InstructionReach::Call(*callee),
        Inst::SeqMap { fwd, .. } => InstructionReach::SeqMap(*fwd),
        Inst::CallIndirect {
            callee,
            sig,
            calling_conv,
            ..
        } | Inst::CallIndirectCannotUnwind { callee, sig, calling_conv, .. }
        | Inst::InvokeIndirect { callee, sig, calling_conv, .. } => InstructionReach::Indirect {
            callee: *callee,
            sig: *sig,
            calling_conv: *calling_conv,
        },
        Inst::GlobalAddr { global } => InstructionReach::Global(*global),
        Inst::Const { value, ty } => InstructionReach::Constant(value, ty),
        Inst::MakeClosure { ty, func, .. } => InstructionReach::Closure(*ty, *func),
        Inst::Switch { cases, .. } => InstructionReach::Cases(cases),
        // A drop names only its type and its pointer. Amendment D (§20): with
        // a drop-glue row it IS a call of the glue; without one the
        // destructor stays IMPLICIT in the instruction (refused below).
        Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => match drop_glue.resolve(ty) {
            crate::DropResolution::Resolved(glue) => InstructionReach::DropGlue(glue),
            crate::DropResolution::Unresolved | crate::DropResolution::Ambiguous => {
                InstructionReach::Drop(ty)
            }
        },
        Inst::DialectOp(_) => InstructionReach::Opaque,
        Inst::Cast {
            op, src_ty, dst_ty, ..
        } => InstructionReach::Cast {
            op: *op,
            src: src_ty,
            dst: dst_ty,
        },
        // Amendment P: a sited check names its panic entry and location; an
        // unsited one still needs the implicit panic runtime.
        Inst::Assert { site: Some(site), .. } | Inst::AssertInvoke { site, .. } => {
            InstructionReach::PanicSite {
                entry: site.entry,
                global: site.location_global(),
            }
        }
        Inst::Assert { site: None, .. } => InstructionReach::Runtime(RuntimeService::Panic),
        Inst::HeapAlloc { origin, .. } => {
            InstructionReach::Runtime(RuntimeService::Allocate(*origin))
        }
        Inst::Dealloc { .. } => InstructionReach::Runtime(RuntimeService::Deallocate),
        Inst::Retain { .. } | Inst::Release { .. } | Inst::IsUnique { .. } => {
            InstructionReach::Runtime(RuntimeService::ReferenceCount)
        }
        // These forms carry no explicit module function/global identity, no
        // constant child, and no implicit runtime service. Keep this
        // exhaustive: a new instruction needs review.
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Return { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::NullPtr
        | Inst::Undef { .. }
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::Assume { .. }
        | Inst::Unreachable
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        // Unwinding within the frame: the landing pad's cleanups are explicit
        // instructions, scanned like any other.
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::MakeAggregate { .. }
        // v50: `n` copies of one register operand.
        | Inst::ArraySplat { .. }
        // Two register tensors and an inline result type: no function, global
        // or symbol (its types are scanned like any other node's).
        | Inst::TensorContract { .. }
        // PKG-U13c: register tensors, scalar lanes and `usize` parameters,
        // with inline types: no function, global or symbol.
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        // PKG-U13d: register tensors (data, coordinates, source) with an
        // inline result type: no function, global or symbol.
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => InstructionReach::Nothing,
    }
}

struct Walker<'module> {
    census: FunctionDependencyCensus<'module>,
    index: ModuleIndex<'module>,
    structs: NamedIndex,
    enums: NamedIndex,
    records: NamedIndex,
    pending: VecDeque<DependencyNode>,
}

impl<'module> Walker<'module> {
    fn new(module: &'module Module, root: FuncId) -> Self {
        let mut walker = Self {
            census: FunctionDependencyCensus {
                module,
                root,
                nodes: BTreeSet::new(),
                edges: Vec::new(),
                refusals: Vec::new(),
            },
            index: ModuleIndex::new(module),
            structs: named_index(module.structs.iter().map(|item| item.id.index())),
            enums: named_index(module.enums.iter().map(|item| item.id.index())),
            records: named_index(module.records.iter().map(|item| item.id.index())),
            pending: VecDeque::new(),
        };
        for refusal in walker.index.module_refusals(module) {
            walker.refuse(DependencySite::Module, refusal);
        }
        walker
    }

    fn edge(&mut self, site: DependencySite, target: DependencyNode) {
        self.census.edges.push(DependencyEdge { site, target });
        if self.census.nodes.insert(target) {
            self.pending.push_back(target);
        }
    }

    fn refuse(&mut self, site: DependencySite, kind: DependencyRefusalKind) {
        self.census.refusals.push(DependencyRefusal { site, kind });
    }

    fn missing(&mut self, node: DependencyNode) {
        self.refuse(
            DependencySite::Definition(node),
            DependencyRefusalKind::Missing(node),
        );
    }

    fn named_position(
        &mut self,
        node: DependencyNode,
        position: Option<Option<usize>>,
    ) -> Option<usize> {
        match position {
            Some(Some(position)) => Some(position),
            Some(None) => {
                self.refuse(
                    DependencySite::Definition(node),
                    DependencyRefusalKind::Ambiguous(node),
                );
                None
            }
            None => {
                self.missing(node);
                None
            }
        }
    }

    fn expand(&mut self, node: DependencyNode) {
        let module = self.census.module;
        let site = DependencySite::Definition(node);
        match node {
            DependencyNode::Function(id) => match self.index.function(id) {
                Ok(function) => self.function(function),
                Err(reason) => self.refuse(site, reason),
            },
            DependencyNode::Global(id) => {
                if let Some(global) = module.globals.get(id.as_usize()) {
                    self.ty(site, &global.ty);
                    match &global.initializer {
                        Some(value) => self.constant(site, value),
                        None => {
                            self.refuse(site, DependencyRefusalKind::MissingGlobalInitializer(id))
                        }
                    }
                } else {
                    self.missing(node);
                }
            }
            DependencyNode::Type(id) => {
                if let Some(ty) = module.types.get(id.as_usize()) {
                    self.ty(site, ty);
                } else {
                    self.missing(node);
                }
            }
            DependencyNode::FunctionType(id) => {
                if let Some(signature) = module.func_types.get(id.as_usize()) {
                    for ty in signature.params.iter().chain(&signature.returns) {
                        self.ty(site, ty);
                    }
                } else {
                    self.missing(node);
                }
            }
            DependencyNode::Struct(id) => {
                if let Some(position) =
                    self.named_position(node, self.structs.get(&id.index()).copied())
                {
                    for field in &module.structs[position].fields {
                        self.ty(site, &field.ty);
                    }
                }
            }
            DependencyNode::Enum(id) => {
                if let Some(position) =
                    self.named_position(node, self.enums.get(&id.index()).copied())
                {
                    for variant in &module.enums[position].variants {
                        for ty in &variant.fields {
                            self.ty(site, ty);
                        }
                    }
                }
            }
            DependencyNode::Record(id) => {
                if let Some(position) =
                    self.named_position(node, self.records.get(&id.index()).copied())
                {
                    for field in &module.records[position].fields {
                        self.ty(site, &field.ty);
                    }
                }
            }
            DependencyNode::ClosureType(id) => {
                if let Some(closure) = module.closure_types.get(id.as_usize()) {
                    self.edge(site, DependencyNode::FunctionType(closure.func));
                    for ty in &closure.captures {
                        self.ty(site, ty);
                    }
                } else {
                    self.missing(node);
                }
            }
            DependencyNode::Predicate(id) => match module.predicates.get(id.as_usize()) {
                Some(Pred::Conj(children) | Pred::Disj(children)) => {
                    for child in children {
                        self.edge(site, DependencyNode::Predicate(*child));
                    }
                }
                Some(Pred::InUniverse(universe, _)) => {
                    self.edge(site, DependencyNode::Universe(*universe))
                }
                Some(Pred::FiniteSet(values)) => {
                    for value in values {
                        self.constant(site, value);
                    }
                }
                Some(
                    Pred::Interval { .. }
                    | Pred::NonZero
                    | Pred::NonNull
                    | Pred::Top
                    | Pred::Bottom,
                ) => {}
                None => self.missing(node),
            },
            DependencyNode::Universe(id) => match module.universes.get(id.as_usize()) {
                Some(Universe::Members(values)) => {
                    for value in values {
                        self.constant(site, value);
                    }
                }
                Some(Universe::IntRange { .. }) => {}
                None => self.missing(node),
            },
        }
    }

    fn function(&mut self, function: &'module Function) {
        let site = DependencySite::Definition(DependencyNode::Function(function.id));
        self.edge(site, DependencyNode::FunctionType(function.ty));
        for refusal in body_shape_refusals(function) {
            self.refuse(site, refusal);
        }
        let pointers = StaticFunctionPointerAnalysis::new(function);
        for block in &function.blocks {
            for (_, ty) in &block.params {
                self.ty(site, ty);
            }
            for (index, node) in block.body.iter().enumerate() {
                let site = DependencySite::Instruction {
                    function: function.id,
                    block: block.id,
                    index,
                };
                node.inst.visit_types(|ty| self.type_occurrence(site, ty));
                match instruction_reach(&node.inst, &self.index.drop_glue) {
                    InstructionReach::Call(callee)
                    | InstructionReach::SeqMap(callee)
                    | InstructionReach::DropGlue(callee) => {
                        self.edge(site, DependencyNode::Function(callee))
                    }
                    InstructionReach::Global(global) => {
                        self.edge(site, DependencyNode::Global(global))
                    }
                    InstructionReach::Closure(ty, func) => {
                        self.edge(site, DependencyNode::ClosureType(ty));
                        self.edge(site, DependencyNode::Function(func));
                    }
                    InstructionReach::PanicSite { entry, global } => {
                        self.edge(site, DependencyNode::Function(entry));
                        if let Some(global) = global {
                            self.edge(site, DependencyNode::Global(global));
                        }
                    }
                    InstructionReach::Constant(value, _) => self.constant(site, value),
                    InstructionReach::Cases(cases) => {
                        for case in cases {
                            self.constant(site, &case.value);
                        }
                    }
                    InstructionReach::Indirect {
                        callee,
                        sig,
                        calling_conv,
                    } => {
                        self.edge(site, DependencyNode::FunctionType(sig));
                        if let Some(resolution) = pointers.resolve_typed_at(callee, block.id, index)
                        {
                            let target = resolution.function();
                            self.edge(site, DependencyNode::Function(target));
                            if !exact_indirect_target(
                                &self.index.functions,
                                &resolution,
                                sig,
                                calling_conv,
                            ) {
                                self.refuse(site, DependencyRefusalKind::IndirectSignatureMismatch);
                            }
                        } else {
                            self.refuse(site, DependencyRefusalKind::IndirectCall);
                        }
                    }
                    InstructionReach::Opaque => {
                        self.refuse(site, DependencyRefusalKind::OpaqueDialectOperation)
                    }
                    // The destructor is a dependency the module does not name:
                    // refuse rather than silently lose it.
                    InstructionReach::Drop(ty) => {
                        self.refuse(site, DependencyRefusalKind::ImplicitDestructor(ty.clone()))
                    }
                    // Casts name no identity; runtime services are outside this
                    // census (module docs) and are classified by the
                    // reachability builder instead.
                    InstructionReach::Cast { .. }
                    | InstructionReach::Runtime(_)
                    | InstructionReach::Nothing => {}
                }
            }
        }
    }

    fn constant(&mut self, site: DependencySite, value: &'module Constant) {
        value.visit_constants(|value| match constant_reach(value) {
            ConstantReach::Function(function) | ConstantReach::Closure(function) => {
                self.edge(site, DependencyNode::Function(function))
            }
            ConstantReach::Symbol(symbol) => match self.index.symbols.resolve(symbol) {
                Ok(target) => self.edge(site, target),
                Err(reason) => self.refuse(site, reason),
            },
            ConstantReach::Nothing => {}
        });
    }

    fn ty(&mut self, site: DependencySite, ty: &'module Ty) {
        ty.visit_types(|ty| self.type_occurrence(site, ty));
    }

    fn type_occurrence(&mut self, site: DependencySite, ty: &Ty) {
        match ty {
            Ty::Storage(_) => {}
            Ty::Struct(id) => self.edge(site, DependencyNode::Struct(*id)),
            Ty::Enum(id) => self.edge(site, DependencyNode::Enum(*id)),
            Ty::Record(id) => self.edge(site, DependencyNode::Record(*id)),
            Ty::Func(id) => self.edge(site, DependencyNode::FunctionType(*id)),
            Ty::Closure(id) => self.edge(site, DependencyNode::ClosureType(*id)),
            Ty::Array(id, _)
            | Ty::Set(id, _)
            | Ty::Sequence(id)
            | Ty::FatPtr(FatPtrKind::Slice(id)) => self.edge(site, DependencyNode::Type(*id)),
            Ty::Refine(base, predicate) => {
                self.edge(site, DependencyNode::Type(*base));
                self.edge(site, DependencyNode::Predicate(*predicate));
            }
            Ty::Error
            | Ty::Dialect(_)
            | Ty::Handle(_)
            | Ty::FatPtr(FatPtrKind::TraitObject { .. }) => {
                self.refuse(site, DependencyRefusalKind::OpaqueType)
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
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
            | Ty::Vector(..)
            // The element is an inline child, visited by `visit_types` itself.
            | Ty::Tensor(..)
            | Ty::Tuple(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::FatPtr(
                FatPtrKind::Str | FatPtrKind::ContainerLen | FatPtrKind::ContainerVtable,
            ) => {}
            Ty::Ext(e) => e.unreachable(),
        }
    }
}

// ===========================================================================
// The reachability engine (spawn census, design 2026-09-29 §5)
// ===========================================================================

/// Gives every graph its own identity, so a handle is never valid in another.
static NEXT_GRAPH: AtomicU64 = AtomicU64::new(0);

/// A node of one [`ReachGraph`]: a handle that graph issued. A fact naming a
/// handle from another graph is a defect ([`ReachDefect::ForeignNode`]),
/// never a silent alias of a node at the same index, and a census asked
/// about one answers UNKNOWN.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReachNode {
    graph: u64,
    index: u32,
}

impl ReachNode {
    fn new(graph: u64, index: usize) -> Self {
        Self {
            graph,
            index: u32::try_from(index).unwrap_or(u32::MAX),
        }
    }

    /// The node's position in its own graph.
    #[must_use]
    pub fn index(self) -> usize {
        self.index as usize
    }
}

/// The program identity a node stands for. One graph holds one lane, and the
/// two lanes share no node (design 2026-09-29 §5.7).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NodeOrigin {
    /// A function or global of one trust-ir module.
    TrustIr(DependencyNode),
    /// The start of every thread a trust-ir seed declaration (this
    /// function) creates: the std code the new thread runs around the
    /// spawned callable, and a RUN of that callable (Trust design 2026-10-02,
    /// "C1", N-4). It joins no definition and nothing reaches it: it is a
    /// [`SpawnSite::entry`].
    TrustIrThreadStart(FuncId),
    /// An adapter-assigned census instance on the MIR lane.
    Mir(u32),
}

impl NodeOrigin {
    fn is_trust_ir(self) -> bool {
        matches!(
            self,
            NodeOrigin::TrustIr(_) | NodeOrigin::TrustIrThreadStart(_)
        )
    }
}

/// The source definition a node's verdict joins into (rustc's
/// `DefPathHash`; trust-ir has no instances yet, so one function is one
/// definition there).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefinitionKey(pub u128);

/// Whether a node is the crate under census or code it depends on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Locality {
    /// Sees confined pool members.
    Local,
    /// Sees only non-confined pool members; a local frame that hands it a
    /// callable is charged by rule H.
    External,
}

/// What the engine knows of a node's body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeBody {
    /// The adapter emitted every fact of the node: its body's, or an UNKNOWN
    /// sink standing for a body it cannot enumerate.
    Walked,
    /// No body to walk, and the adapter's policy assumes it starts no thread
    /// itself (foreign code, R3). Under rule H it invokes EVERY key.
    Opaque,
    /// Code resolved per concrete instance (R1): reached only through PARAM
    /// edges, its facts belong to its instances, so it has none here.
    Param,
    /// A thread-creation entry point. Terminal: the engine never walks past
    /// it, and it is the only base of a SPAWNS claim.
    Seed,
    /// A primitive (Trust design 2026-10-02, "C1", §3.2): no body is walked;
    /// the adapter emitted the facts of its checked summary
    /// ([`PrimitiveSummary`]). The engine treats it exactly as a walked node
    /// of the same [`Locality`]: not terminal, never the base of a SPAWNS
    /// claim, invoking only the keys its summary lists, and, when local,
    /// charged by rule H for what its invokes hand to external code. An
    /// adapter gives it the locality of the walked body it stands for (the
    /// trust-ir walk: `Local`). Only a thread model reads the difference, as
    /// the primitive's event.
    Primitive,
}

/// A program node an adapter adds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReachNodeSpec {
    pub origin: NodeOrigin,
    /// `None` joins into no definition (a trust-ir global).
    pub definition: Option<DefinitionKey>,
    pub locality: Locality,
    pub body: NodeBody,
}

/// A node: a program node, an UNKNOWN sink, or an engine hub.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReachNodeKind {
    Program(ReachNodeSpec),
    /// A node that cannot be enumerated. It refuses without claiming a spawn.
    Sink(DependencyRefusalKind),
    /// An engine-derived hub: a target list that one or more derivation
    /// facts share (an invoke's pool, or what a hand-off reaches under rule
    /// H). [`ReachGraph::solve`] derives an APPROX edge from each fact's node
    /// to its hub and one from the hub to each target, so the derived edges
    /// number O(facts + targets), never facts × targets. A hub is no code:
    /// no adapter names one, it joins no definition, a witness, a thread
    /// closure and a spawn site look through it, and its label is the
    /// strongest an APPROX edge to one of its targets gives
    /// ([`ExpandedReachGraph::derived_edge_scan`] lists the edges it stands
    /// for).
    Hub,
}

/// Where a fact was observed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReachSite {
    TrustIr(DependencySite),
    /// An adapter-assigned location on the MIR lane.
    Mir(u64),
}

/// Why an edge exists (design 2026-09-29 §2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EdgeClass {
    /// Runs that code.
    Run,
    /// Makes a callable into a function-pointer or `dyn` value.
    Create,
    /// Reads a constant or static that holds one.
    Read,
    /// An indirect call's pool, or a rule H hand-off. Engine-derived only.
    Approx,
    /// Depends on a type parameter; resolved per concrete instance. Admitted
    /// by no verdict (R1).
    Param,
}

impl EdgeClass {
    /// The strongest verdict whose reachability admits this class.
    #[must_use]
    pub fn cap(self) -> Verdict {
        match self {
            EdgeClass::Run => Verdict::Spawns,
            EdgeClass::Create | EdgeClass::Read => Verdict::Escapes,
            EdgeClass::Approx => Verdict::Indirect,
            EdgeClass::Param => Verdict::Quiet,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReachEdge {
    pub from: ReachNode,
    pub to: ReachNode,
    pub class: EdgeClass,
    pub site: ReachSite,
    /// The edge is a destructor run (drop glue): invisible at the source site.
    pub via_drop: bool,
}

/// A node's census verdict, weakest first (design 2026-09-29 §5.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Verdict {
    /// No path to a seed or sink: no refusal.
    Quiet,
    /// Reaches an UNKNOWN sink: "not enumerated (no spawn was found)".
    Unknown,
    /// Reaches a seed through an indirect call's pool or a hand-off.
    Indirect,
    /// Names, erases or reads a spawning callable.
    Escapes,
    /// Reaches a seed through RUN edges only: the only spawn claim.
    Spawns,
}

impl Verdict {
    /// The four labelled reachabilities, strongest first.
    pub const LEVELS: [Verdict; 4] = [
        Verdict::Spawns,
        Verdict::Escapes,
        Verdict::Indirect,
        Verdict::Unknown,
    ];

    /// Whether the verdict refuses the function.
    #[must_use]
    pub fn refuses(self) -> bool {
        self != Verdict::Quiet
    }

    /// Whether the verdict claims a spawn.
    #[must_use]
    pub fn claims_spawn(self) -> bool {
        self == Verdict::Spawns
    }
}

/// A malformed fact. Any defect turns every node UNKNOWN.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReachDefect {
    /// Nodes of both lanes in one graph.
    MixedOrigins,
    /// A handle this graph did not issue.
    ForeignNode(ReachNode),
    /// An edge out of a seed or a sink, which are terminal.
    EdgeFromTerminal(ReachNode),
    /// A sink where a program node is required.
    NotAProgramNode(ReachNode),
    /// A spawn fact whose callee is not a seed.
    SpawnOfNonSeed(ReachNode),
    /// An APPROX edge pushed by an adapter; only the engine derives them.
    AdapterApprox,
    /// More nodes than a `u32` handle can name.
    TooLarge,
}

/// Facts from ONE adapter, before solving.
#[derive(Debug)]
#[cfg_attr(test, derive(Clone))]
pub struct ReachGraph {
    id: u64,
    nodes: Vec<ReachNodeKind>,
    edges: Vec<ReachEdge>,
    universe: IndirectCallUniverse,
    /// Spawned entry per RUN edge into a seed, by edge index.
    thread_entries: BTreeMap<usize, Option<ReachNode>>,
    lane: Option<bool>,
    defects: Vec<ReachDefect>,
}

impl Default for ReachGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl ReachGraph {
    #[must_use]
    pub fn new() -> Self {
        Self {
            id: NEXT_GRAPH.fetch_add(1, Ordering::Relaxed),
            nodes: Vec::new(),
            edges: Vec::new(),
            universe: IndirectCallUniverse::default(),
            thread_entries: BTreeMap::new(),
            lane: None,
            defects: Vec::new(),
        }
    }

    /// Add a program node.
    pub fn add_node(&mut self, spec: ReachNodeSpec) -> ReachNode {
        let lane = spec.origin.is_trust_ir();
        if *self.lane.get_or_insert(lane) != lane {
            self.defect(ReachDefect::MixedOrigins);
        }
        self.push(ReachNodeKind::Program(spec))
    }

    fn push(&mut self, kind: ReachNodeKind) -> ReachNode {
        let node = ReachNode::new(self.id, self.nodes.len());
        self.nodes.push(kind);
        node
    }

    fn defect(&mut self, defect: ReachDefect) {
        if !self.defects.contains(&defect) {
            self.defects.push(defect);
        }
    }

    fn kind(&self, node: ReachNode) -> Option<&ReachNodeKind> {
        if node.graph != self.id {
            return None;
        }
        self.nodes.get(node.index())
    }

    /// Record a defect unless `node` is a program node of this graph.
    fn program(&mut self, node: ReachNode) -> bool {
        match self.kind(node) {
            Some(ReachNodeKind::Program(_)) => true,
            // A hub exists only after solving; an adapter never holds one.
            Some(ReachNodeKind::Sink(_) | ReachNodeKind::Hub) => {
                self.defect(ReachDefect::NotAProgramNode(node));
                false
            }
            None => {
                self.defect(ReachDefect::ForeignNode(node));
                false
            }
        }
    }

    fn is_seed(&self, node: ReachNode) -> bool {
        matches!(
            self.kind(node),
            Some(ReachNodeKind::Program(ReachNodeSpec {
                body: NodeBody::Seed,
                ..
            }))
        )
    }

    /// Record a defect unless an edge may leave `node`.
    fn source(&mut self, node: ReachNode) -> bool {
        if !self.program(node) {
            return false;
        }
        if self.is_seed(node) {
            self.defect(ReachDefect::EdgeFromTerminal(node));
            return false;
        }
        true
    }

    /// Add an edge. `Approx` is engine-derived; an adapter's is a defect.
    pub fn add_edge(
        &mut self,
        from: ReachNode,
        to: ReachNode,
        class: EdgeClass,
        site: ReachSite,
        via_drop: bool,
    ) {
        if class == EdgeClass::Approx {
            self.defect(ReachDefect::AdapterApprox);
        }
        if !self.source(from) {
            return;
        }
        if self.kind(to).is_none() {
            self.defect(ReachDefect::ForeignNode(to));
            return;
        }
        self.edges.push(ReachEdge {
            from,
            to,
            class,
            site,
            via_drop,
        });
    }

    /// Add a fresh UNKNOWN sink and an edge to it from `from`. Any sink also
    /// leaves every pool unclosed ([`ClosedPools::unclosed`]): the code or
    /// data it stands for may have minted a callable no CREATE records.
    pub fn add_unknown(
        &mut self,
        from: ReachNode,
        reason: DependencyRefusalKind,
        class: EdgeClass,
        site: ReachSite,
        via_drop: bool,
    ) -> ReachNode {
        let sink = self.push(ReachNodeKind::Sink(reason));
        self.add_edge(from, sink, class, site, via_drop);
        sink
    }

    /// A call of a seed that starts a new thread at `entry` (`None` when the
    /// adapter cannot name the spawned callable; see [`SpawnSite::entry`]).
    /// Adds the RUN edge.
    pub fn add_spawn(
        &mut self,
        caller: ReachNode,
        seed: ReachNode,
        entry: Option<ReachNode>,
        site: ReachSite,
        via_drop: bool,
    ) {
        if !self.is_seed(seed) {
            self.defect(ReachDefect::SpawnOfNonSeed(seed));
            return;
        }
        if let Some(entry) = entry
            && !self.program(entry)
        {
            return;
        }
        let edges = self.edges.len();
        self.add_edge(caller, seed, EdgeClass::Run, site, via_drop);
        if self.edges.len() > edges {
            self.thread_entries.insert(edges, entry);
        }
    }

    /// `creator` makes `member` into a callable value of `key`: a CREATE edge
    /// and pool membership.
    pub fn add_create(
        &mut self,
        creator: ReachNode,
        member: ReachNode,
        key: PoolKey,
        confined: bool,
        site: ReachSite,
    ) {
        self.add_edge(creator, member, EdgeClass::Create, site, false);
        self.add_pool_member(member, key, confined);
    }

    /// Pool membership with no CREATE edge: a vtable drop slot minted through
    /// a shared `&` (the `&`-erasure rule) still joins its DynDropPool.
    pub fn add_pool_member(&mut self, member: ReachNode, key: PoolKey, confined: bool) {
        if self.program(member) {
            self.universe.members.push(PoolMember {
                member,
                key,
                confined,
            });
        }
    }

    /// An indirect call at `node` charged by `key`. `carried` is what its
    /// operands carry, for rule H when a pool member is external code.
    pub fn add_invoke(
        &mut self,
        node: ReachNode,
        key: PoolKey,
        carried: Vec<CarriedKey>,
        site: ReachSite,
        via_drop: bool,
    ) {
        if self.source(node) {
            self.universe.invokes.push(PoolInvoke {
                node,
                key,
                carried,
                site,
                via_drop,
            });
        }
    }

    /// A local frame passing operands that carry `carried` to external
    /// `callee`. A hand-off that carries nothing is no fact.
    pub fn add_handoff(
        &mut self,
        node: ReachNode,
        callee: ReachNode,
        carried: Vec<CarriedKey>,
        site: ReachSite,
        via_drop: bool,
    ) {
        if self.source(node) && self.program(callee) && !carried.is_empty() {
            self.universe.handoffs.push(PoolHandoff {
                node,
                callee,
                carried,
                site,
                via_drop,
            });
        }
    }

    /// A LAUNDER of a callable the adapter cannot name (running inline
    /// assembly; on the trust-ir lane, every reinterpreting cast of a
    /// callable-carrying type): a LAUNDER of [`CarriedKey::Any`], so no member
    /// stays confined and data ([`CarriedKey::Laundered`]) may carry any
    /// callable. The FnPools stay keyed by shape: a laundered callable called
    /// back at a shape its own does not match is UB (R4,
    /// [`ClosedPools::pool`]).
    pub fn add_launder(&mut self, site: ReachSite) {
        self.add_launder_keys(site, vec![CarriedKey::Any]);
    }

    /// A LAUNDER whose reinterpreted bytes may hold callables of `keys`: data
    /// ([`CarriedKey::Laundered`]) may then hold what `keys` admit, and a key
    /// naming a principal demotes its confined members as a LIFETIME-ERASE
    /// does ([`CarriedKey::Any`] and [`CarriedKey::AnyDyn`] demote every one).
    ///
    /// Sound only while EVERY route by which a callable's bytes reach data is
    /// recorded with keys covering them (a value reinterpretation, a pointer
    /// view at another pointee, a union field, a reshaped fn pointer's
    /// parameter, an exposed address, a constant's bytes): `add_launder_of`
    /// (`e0d69a95`, withdrawn in `953caecb`) narrowed data while pointer and
    /// union puns went unrecorded. A key here is a key of the reinterpreted
    /// bytes' type, never of one known callable. [`CarriedKey::Laundered`] in
    /// `keys` is dropped (data read as data launders nothing); no keys, no
    /// fact.
    pub fn add_launder_keys(&mut self, site: ReachSite, keys: Vec<CarriedKey>) {
        let mut recorded = false;
        for key in keys {
            if key == CarriedKey::Laundered {
                continue;
            }
            self.universe.laundered.entry(key).or_insert(site);
            recorded = true;
        }
        if recorded {
            self.universe.launder.get_or_insert(site);
        }
    }

    /// A `&dyn principal` cast to a raw pointer or transmuted: its confined
    /// members are demoted.
    pub fn add_lifetime_erase(&mut self, principal: PrincipalKey) {
        self.universe.erased.insert(principal);
    }

    /// A `dyn` → `dyn` unsize that changes the principal.
    pub fn add_upcast(&mut self, from: PrincipalKey, to: PrincipalKey) {
        self.universe.upcasts.insert((from, to));
    }

    /// Close the pools, derive the APPROX edges, label every node, check the
    /// labelling, and adopt it — or, on any defect or rejection, refuse every
    /// node as UNKNOWN.
    #[must_use]
    pub fn solve(self) -> ReachCensus {
        let expanded = self.expand();
        let solution = expanded.solve_levels();
        ReachCensus::adopt(expanded, solution)
    }

    fn expand(self) -> ExpandedReachGraph {
        let unenumerated = self
            .nodes
            .iter()
            .any(|kind| matches!(kind, ReachNodeKind::Sink(_)));
        let pools = self.universe.close(unenumerated);
        let mut expanded = ExpandedReachGraph {
            graph: self.id,
            base_edges: self.edges.len(),
            nodes: self.nodes,
            edges: self.edges,
            thread_entries: self.thread_entries,
            defects: self.defects,
            pools,
            derived: Derived::default(),
        };
        if expanded.defects.is_empty() {
            expanded.derive_approx(&self.universe);
        }
        expanded
    }
}

/// The graph a labelling is checked against: the adapter's edges followed by
/// the engine-derived APPROX edges, compressed through hubs
/// ([`ReachNodeKind::Hub`]).
#[derive(Debug)]
pub struct ExpandedReachGraph {
    graph: u64,
    nodes: Vec<ReachNodeKind>,
    edges: Vec<ReachEdge>,
    base_edges: usize,
    thread_entries: BTreeMap<usize, Option<ReachNode>>,
    defects: Vec<ReachDefect>,
    pools: ClosedPools,
    derived: Derived,
}

/// Indexed by position in [`Verdict::LEVELS`].
type LevelParents = [Vec<u32>; 4];
const NO_PARENT: u32 = u32::MAX;

/// The engine sinks [`ExpandedReachGraph::derive_approx`] adds: one per open
/// principal, and one for the unclosed pools (`None`).
type EngineSinks = BTreeMap<Option<PrincipalKey>, ReachNode>;

/// The engine-derived APPROX edges, compressed.
///
/// A derivation FACT is one invoke, or one round of one hand-off under rule H
/// (all of one local invoke's hand-offs to its pool's external members are
/// one fact), and names a HUB: the target list it derives APPROX edges to.
/// The edges the facts stand for, the LOGICAL derived edges, are every
/// `(fact.from, target)` pair in fact order and, within a fact, in target
/// order; a repeated pair keeps its first position and is flagged `via_drop`
/// only if every fact behind it is (its site is then the first such fact's
/// that is not). That is, edge for edge and in the same order, the list the
/// uncompressed derivation builds (the `reference` test module keeps it and
/// compares the two), and every verdict, witness, spawn site and thread
/// closure is that list's. Stored, it is O(facts + hub targets): a pool is
/// one hub however many sites invoke it, so a census never holds the
/// sites × members product of a large pool.
#[derive(Debug, Default)]
struct Derived {
    facts: Vec<DerivedFact>,
    hubs: Vec<Hub>,
    /// Each node's facts, ascending (indexed below `hub_base`).
    facts_from: Vec<Vec<u32>>,
    /// The hubs holding each node, by ascending hub, with its position in
    /// that hub's targets (indexed below `hub_base`).
    hubs_of: Vec<Vec<(u32, u32)>>,
    /// The node index of hub 0: every hub sits after every other node.
    hub_base: usize,
}

#[derive(Debug, Clone, Copy)]
struct DerivedFact {
    from: ReachNode,
    site: ReachSite,
    via_drop: bool,
    hub: u32,
    /// The compressed edge `from -> hub`.
    edge: u32,
}

#[derive(Debug)]
struct Hub {
    /// No target twice.
    targets: Vec<ReachNode>,
    /// The facts naming this hub, ascending.
    facts: Vec<u32>,
    /// The compressed edge to `targets[0]`; target `i`'s is `first_edge + i`.
    first_edge: u32,
}

/// A fact before its compressed edge exists.
#[derive(Debug, Clone, Copy)]
struct RawFact {
    from: ReachNode,
    site: ReachSite,
    via_drop: bool,
    hub: u32,
}

/// Where a logical derived edge stands in derivation order: its fact, then
/// its target's position in that fact's hub. Every adapter edge precedes
/// every derived edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DerivedOrder {
    pub fact: u32,
    pub position: u32,
}

/// Target lists, interned by content: facts with equal lists share one hub.
#[derive(Default)]
struct HubTable {
    lists: Vec<Vec<ReachNode>>,
    by_hash: HashMap<u64, Vec<u32>>,
}

impl HubTable {
    /// The hub of `targets`, a repeat dropped where it repeats (the first
    /// stays); `None` for an empty list, which derives nothing.
    fn intern(&mut self, mut targets: Vec<ReachNode>) -> Option<u32> {
        let mut seen: HashSet<ReachNode> = HashSet::with_capacity(targets.len());
        targets.retain(|target| seen.insert(*target));
        if targets.is_empty() {
            return None;
        }
        let mut hasher = DefaultHasher::new();
        targets.hash(&mut hasher);
        let bucket = self.by_hash.entry(hasher.finish()).or_default();
        if let Some(hub) = bucket
            .iter()
            .find(|hub| self.lists[**hub as usize] == targets)
        {
            return Some(*hub);
        }
        let hub = u32::try_from(self.lists.len()).unwrap_or(u32::MAX);
        bucket.push(hub);
        self.lists.push(targets);
        Some(hub)
    }
}

/// The positions of each pool's members in [`ClosedPools::members`],
/// computed once per key: a `dyn` key's by exact key, an fn key's by shape
/// over the fn members only.
struct PoolLookup {
    by_key: HashMap<PoolKey, Vec<usize>>,
    fn_rows: Vec<usize>,
    cache: HashMap<PoolKey, Vec<usize>>,
}

impl PoolLookup {
    fn new(pools: &ClosedPools) -> Self {
        let mut by_key: HashMap<PoolKey, Vec<usize>> = HashMap::new();
        let mut fn_rows = Vec::new();
        for (position, row) in pools.members().iter().enumerate() {
            match row.key {
                PoolKey::Fn(_) => fn_rows.push(position),
                _ => by_key.entry(row.key.clone()).or_default().push(position),
            }
        }
        Self {
            by_key,
            fn_rows,
            cache: HashMap::new(),
        }
    }

    /// What [`ClosedPools::pool`] yields for `key`, as member positions.
    fn pool(&mut self, pools: &ClosedPools, key: &PoolKey) -> &[usize] {
        if !self.cache.contains_key(key) {
            let rows: Vec<usize> = match key {
                PoolKey::Fn(_) => self
                    .fn_rows
                    .iter()
                    .copied()
                    .filter(|position| pools.in_pool(key, &pools.members()[*position]))
                    .collect(),
                _ => self.by_key.get(key).cloned().unwrap_or_default(),
            };
            self.cache.insert(key.clone(), rows);
        }
        self.cache.get(key).map_or(&[], Vec::as_slice)
    }
}

/// One local invoke's hand-offs to the external members of its pool (rule H
/// at an indirect call): one per member, consecutive in hand-off order, so
/// one fact per round.
struct ImplicitGroup {
    node: ReachNode,
    carried: Vec<CarriedKey>,
    site: ReachSite,
    via_drop: bool,
    /// Index into the external member lists.
    callees: usize,
}

/// The state of one derivation: everything [`ExpandedReachGraph::derive_approx`]
/// computes besides the adapter's edges and the pools.
struct Derivation<'pools> {
    graph: u64,
    pools: &'pools ClosedPools,
    sinks: EngineSinks,
    lookup: PoolLookup,
    hubs: HubTable,
    facts: Vec<RawFact>,
    /// Rule H target lists, sorted by node as a set of them is.
    parts: Vec<Vec<ReachNode>>,
    /// The part of a hand-off to a callee that may invoke every key, by
    /// what it carries (the same in every round).
    every: HashMap<Vec<CarriedKey>, Option<usize>>,
    /// The part of a hand-off straight into a thread start.
    seed_parts: HashMap<ReachNode, usize>,
    /// The hub of a hand-off's parts, by its parts.
    part_hubs: HashMap<Vec<usize>, Option<u32>>,
}

impl Derivation<'_> {
    /// The engine sink for an open `principal`, or for the unclosed pools,
    /// created on first use, after every node there is.
    fn sink(
        &mut self,
        nodes: &mut Vec<ReachNodeKind>,
        principal: Option<PrincipalKey>,
    ) -> ReachNode {
        if let Some(sink) = self.sinks.get(&principal) {
            return *sink;
        }
        let sink = ReachNode::new(self.graph, nodes.len());
        nodes.push(ReachNodeKind::Sink(match principal {
            Some(_) => DependencyRefusalKind::OpenPrincipal,
            None => DependencyRefusalKind::UnclosedPool,
        }));
        self.sinks.insert(principal, sink);
        sink
    }

    fn part(&mut self, targets: BTreeSet<ReachNode>) -> Option<usize> {
        if targets.is_empty() {
            return None;
        }
        self.parts.push(targets.into_iter().collect());
        Some(self.parts.len() - 1)
    }

    /// The hub of a hand-off whose callees' parts are `parts`, in callee
    /// order: their lists one after the other, each repeat dropped.
    fn part_hub(&mut self, parts: Vec<usize>) -> Option<u32> {
        if let Some(hub) = self.part_hubs.get(&parts) {
            return *hub;
        }
        let targets: Vec<ReachNode> = parts
            .iter()
            .flat_map(|part| self.parts[*part].iter().copied())
            .collect();
        let hub = self.hubs.intern(targets);
        self.part_hubs.insert(parts, hub);
        hub
    }
}

/// The parts of hand-offs to callees that invoke some keys, by what the
/// hand-off carries, then by the callee's component.
type SomeParts = HashMap<Vec<CarriedKey>, HashMap<usize, Option<usize>>>;

/// What one round of rule H reads.
struct RoundContext<'round> {
    summaries: &'round InvokedKeySummaries,
    invokes: &'round [PoolInvoke],
    runs_into_seed: &'round BTreeSet<(ReachNode, ReachNode)>,
    unclosed: bool,
}

impl ExpandedReachGraph {
    /// Every node with its handle, in index order (sinks and hubs included).
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = (ReachNode, &ReachNodeKind)> + '_ {
        self.nodes
            .iter()
            .enumerate()
            .map(|(index, kind)| (ReachNode::new(self.graph, index), kind))
    }

    #[must_use]
    pub fn node(&self, node: ReachNode) -> Option<&ReachNodeKind> {
        self.local(node).map(|index| &self.nodes[index])
    }

    /// Every edge the labelling is checked against: the first
    /// [`Self::adapter_edge_count`] came from the adapter; the rest are the
    /// engine-derived APPROX edges, compressed through hubs (each fact's node
    /// to its hub, each hub to its targets). The derived edges they stand
    /// for are [`Self::derived_edge_scan`]'s, and [`Self::logical_edges`]
    /// lists every edge uncompressed.
    #[must_use]
    pub fn edges(&self) -> &[ReachEdge] {
        &self.edges
    }

    #[must_use]
    pub fn adapter_edge_count(&self) -> usize {
        self.base_edges
    }

    #[must_use]
    pub fn pools(&self) -> &ClosedPools {
        &self.pools
    }

    /// Whether `node` is an engine hub ([`ReachNodeKind::Hub`]).
    #[must_use]
    pub fn is_hub(&self, node: ReachNode) -> bool {
        matches!(self.node(node), Some(ReachNodeKind::Hub))
    }

    /// How many hubs and derivation facts the derived edges are stored as.
    #[must_use]
    pub fn derivation_size(&self) -> (usize, usize) {
        (self.derived.hubs.len(), self.derived.facts.len())
    }

    /// A reusable lister of each node's logical derived edges.
    #[must_use]
    pub fn derived_edge_scan(&self) -> DerivedEdgeScan<'_> {
        let count = self.derived.facts_from.len();
        DerivedEdgeScan {
            graph: self,
            stamp: vec![0; count],
            slot: vec![0; count],
            epoch: 0,
            edges: Vec::new(),
        }
    }

    /// Every logical edge, uncompressed and in order: the adapter's, then
    /// every derived edge in derivation order. It holds the sites × members
    /// product a hub saves, so it is for tests and small graphs; a census
    /// reads [`Self::derived_edge_scan`] node by node.
    #[must_use]
    pub fn logical_edges(&self) -> Vec<ReachEdge> {
        let mut derived: Vec<(DerivedOrder, ReachEdge)> = Vec::new();
        let mut scan = self.derived_edge_scan();
        for index in 0..self.derived.facts_from.len() {
            derived.extend_from_slice(scan.edges_from(self.handle(index)));
        }
        derived.sort_by_key(|(order, _)| *order);
        self.edges[..self.base_edges]
            .iter()
            .copied()
            .chain(derived.into_iter().map(|(_, edge)| edge))
            .collect()
    }

    /// The logical derived edge `from -> to`, if the derivation holds it:
    /// the first fact of `from` whose hub holds `to` places it, and its site
    /// is the first such fact's that is not `via_drop`, if one is.
    fn logical_edge(&self, from: ReachNode, to: ReachNode) -> Option<ReachEdge> {
        let holders = self.derived.hubs_of.get(to.index())?;
        let mut found: Option<ReachEdge> = None;
        for &fact in self.derived.facts_from.get(from.index())? {
            let fact = &self.derived.facts[fact as usize];
            if holders
                .binary_search_by_key(&fact.hub, |(hub, _)| *hub)
                .is_err()
            {
                continue;
            }
            match &mut found {
                None => {
                    found = Some(ReachEdge {
                        from,
                        to,
                        class: EdgeClass::Approx,
                        site: fact.site,
                        via_drop: fact.via_drop,
                    });
                }
                Some(edge) => {
                    if edge.via_drop && !fact.via_drop {
                        edge.via_drop = false;
                        edge.site = fact.site;
                    }
                }
            }
            if found.is_some_and(|edge| !edge.via_drop) {
                break;
            }
        }
        found
    }

    /// `node`'s index, if this graph issued it.
    fn local(&self, node: ReachNode) -> Option<usize> {
        (node.graph == self.graph && node.index() < self.nodes.len()).then_some(node.index())
    }

    fn handle(&self, index: usize) -> ReachNode {
        ReachNode::new(self.graph, index)
    }

    fn spec(&self, node: ReachNode) -> Option<&ReachNodeSpec> {
        match self.node(node) {
            Some(ReachNodeKind::Program(spec)) => Some(spec),
            Some(ReachNodeKind::Sink(_) | ReachNodeKind::Hub) | None => None,
        }
    }

    fn is_seed(&self, node: usize) -> bool {
        matches!(
            self.nodes[node],
            ReachNodeKind::Program(ReachNodeSpec {
                body: NodeBody::Seed,
                ..
            })
        )
    }

    fn is_sink(&self, node: usize) -> bool {
        matches!(self.nodes[node], ReachNodeKind::Sink(_))
    }

    fn is_hub_index(&self, node: usize) -> bool {
        matches!(self.nodes.get(node), Some(ReachNodeKind::Hub))
    }

    /// The label a base node must carry, if `node` is a base.
    fn base_label(&self, node: usize) -> Option<Verdict> {
        if self.is_seed(node) {
            Some(Verdict::Spawns)
        } else if self.is_sink(node) {
            Some(Verdict::Unknown)
        } else {
            None
        }
    }

    /// Derive the APPROX edges: every invoke to its visible pool members (and
    /// to an UNKNOWN sink for an open principal, or for unclosed pools), then
    /// rule H to a fixpoint. They are kept as facts naming hubs ([`Derived`]):
    /// the logical edges, their order, their sites and the engine sinks'
    /// nodes are exactly those of deriving edge by edge.
    fn derive_approx(&mut self, universe: &IndirectCallUniverse) {
        let pools = std::mem::take(&mut self.pools);
        let mut derivation = Derivation {
            graph: self.graph,
            pools: &pools,
            sinks: EngineSinks::new(),
            lookup: PoolLookup::new(&pools),
            hubs: HubTable::default(),
            facts: Vec::new(),
            parts: Vec::new(),
            every: HashMap::new(),
            seed_parts: HashMap::new(),
            part_hubs: HashMap::new(),
        };
        let unclosed = pools.unclosed();
        // Each invoke is one fact naming its pool's hub. A local invoke whose
        // operands carry a key hands them to each external member of its pool
        // (rule H at an indirect call): one group, derived with the hand-offs.
        let mut invoke_hubs: HashMap<(PoolKey, bool), Option<u32>> = HashMap::new();
        let mut external_of: HashMap<PoolKey, usize> = HashMap::new();
        let mut external_lists: Vec<Vec<ReachNode>> = Vec::new();
        let mut groups: Vec<ImplicitGroup> = Vec::new();
        for invoke in &universe.invokes {
            let local = self
                .spec(invoke.node)
                .is_some_and(|spec| spec.locality == Locality::Local);
            // The engine sinks, created in the order an edge-by-edge
            // derivation creates them: their node indices are part of the
            // result (a set of targets is ordered by node).
            let open = match invoke.key.principal() {
                Some(principal) if pools.open_principals().contains(&principal) => {
                    Some(derivation.sink(&mut self.nodes, Some(principal)))
                }
                _ => None,
            };
            let unclosed_sink = unclosed.then(|| derivation.sink(&mut self.nodes, None));
            let cache_key = (invoke.key.clone(), local);
            let hub = match invoke_hubs.get(&cache_key) {
                Some(hub) => *hub,
                None => {
                    let mut targets: Vec<ReachNode> = derivation
                        .lookup
                        .pool(&pools, &invoke.key)
                        .iter()
                        .map(|position| &pools.members()[*position])
                        .filter(|member| local || !member.confined)
                        .map(|member| member.member)
                        .collect();
                    targets.extend(open);
                    targets.extend(unclosed_sink);
                    let hub = derivation.hubs.intern(targets);
                    invoke_hubs.insert(cache_key, hub);
                    hub
                }
            };
            if let Some(hub) = hub {
                derivation.facts.push(RawFact {
                    from: invoke.node,
                    site: invoke.site,
                    via_drop: invoke.via_drop,
                    hub,
                });
            }
            if local && !invoke.carried.is_empty() {
                let list = match external_of.get(&invoke.key) {
                    Some(list) => *list,
                    None => {
                        let callees: Vec<ReachNode> = derivation
                            .lookup
                            .pool(&pools, &invoke.key)
                            .iter()
                            .map(|position| pools.members()[*position].member)
                            .filter(|member| {
                                self.spec(*member)
                                    .is_some_and(|spec| spec.locality == Locality::External)
                            })
                            .collect();
                        external_lists.push(callees);
                        external_of.insert(invoke.key.clone(), external_lists.len() - 1);
                        external_lists.len() - 1
                    }
                };
                if !external_lists[list].is_empty() {
                    groups.push(ImplicitGroup {
                        node: invoke.node,
                        carried: invoke.carried.clone(),
                        site: invoke.site,
                        via_drop: invoke.via_drop,
                        callees: list,
                    });
                }
            }
        }

        let external_has_seed: Vec<bool> = external_lists
            .iter()
            .map(|callees| callees.iter().any(|callee| self.is_seed(callee.index())))
            .collect();
        let explicit = universe.handoffs.len();
        let slots = explicit + groups.len();
        if slots > 0 {
            let runs_into_seed: BTreeSet<(ReachNode, ReachNode)> = self
                .edges
                .iter()
                .filter(|edge| edge.class == EdgeClass::Run && self.is_seed(edge.to.index()))
                .map(|edge| (edge.from, edge.to))
                .collect();
            let own_base: Vec<Vec<usize>> = {
                let mut own = vec![Vec::new(); self.nodes.len()];
                for (index, invoke) in universe.invokes.iter().enumerate() {
                    own[invoke.node.index()].push(index);
                }
                own
            };
            let everything_base: Vec<bool> = self
                .nodes
                .iter()
                .map(|kind| match kind {
                    ReachNodeKind::Sink(_) => true,
                    ReachNodeKind::Program(spec) => spec.body == NodeBody::Opaque,
                    ReachNodeKind::Hub => false,
                })
                .collect();
            // The hub each hand-off (explicit, then each group) derived to
            // last. A round that gives every one the same hub derives nothing
            // new, so the fixpoint is reached; a fact repeating a hand-off's
            // previous hub would derive no edge and move no site.
            let mut current: Vec<Option<u32>> = vec![None; slots];
            loop {
                // Each round reads the summaries of the graph so far. Hubs
                // are nodes of it, after every other node: a node reaches
                // what it reached through the derived edges, and a hub
                // invokes nothing itself and is not code nobody enumerated.
                let count = self.nodes.len();
                let hubs = derivation.hubs.lists.len();
                let mut successors: Vec<Vec<usize>> = vec![Vec::new(); count + hubs];
                for edge in &self.edges {
                    if matches!(edge.class, EdgeClass::Run | EdgeClass::Approx) {
                        successors[edge.from.index()].push(edge.to.index());
                    }
                }
                for fact in &derivation.facts {
                    successors[fact.from.index()].push(count + fact.hub as usize);
                }
                for (hub, targets) in derivation.hubs.lists.iter().enumerate() {
                    successors[count + hub].extend(targets.iter().map(|target| target.index()));
                }
                let mut own = own_base.clone();
                own.resize(count + hubs, Vec::new());
                let mut everything = everything_base.clone();
                everything.resize(count, true);
                everything.resize(count + hubs, false);
                let summaries = InvokedKeySummaries::new(&successors, &own, &everything);
                drop(successors);
                let context = RoundContext {
                    summaries: &summaries,
                    invokes: &universe.invokes,
                    runs_into_seed: &runs_into_seed,
                    unclosed,
                };
                // The part of a hand-off to a callee that invokes some keys, by
                // what it carries and the callee's component (this round).
                let mut some: SomeParts = HashMap::new();
                // A group's hub by its callee list and what it carries, when
                // no callee is a thread start (whose part depends on the
                // hand-off's node).
                let mut group_hubs: HashMap<(usize, Vec<CarriedKey>), Option<u32>> = HashMap::new();
                let mut changed = false;
                for slot in 0..slots {
                    let (node, site, via_drop, hub) = if slot < explicit {
                        let handoff = &universe.handoffs[slot];
                        let part = self.handoff_part(
                            &mut derivation,
                            &context,
                            &mut some,
                            handoff.node,
                            handoff.callee,
                            &handoff.carried,
                        );
                        let hub = match part {
                            Some(part) => derivation.part_hub(vec![part]),
                            None => None,
                        };
                        (handoff.node, handoff.site, handoff.via_drop, hub)
                    } else {
                        let group = &groups[slot - explicit];
                        let cacheable = !external_has_seed[group.callees];
                        let cached = cacheable
                            .then(|| group_hubs.get(&(group.callees, group.carried.clone())))
                            .flatten()
                            .copied();
                        let hub = match cached {
                            Some(hub) => hub,
                            None => {
                                let mut parts: Vec<usize> = Vec::new();
                                let mut seen: HashSet<usize> = HashSet::new();
                                for callee in &external_lists[group.callees] {
                                    if let Some(part) = self.handoff_part(
                                        &mut derivation,
                                        &context,
                                        &mut some,
                                        group.node,
                                        *callee,
                                        &group.carried,
                                    ) && seen.insert(part)
                                    {
                                        parts.push(part);
                                    }
                                }
                                let hub = if parts.is_empty() {
                                    None
                                } else {
                                    derivation.part_hub(parts)
                                };
                                if cacheable {
                                    group_hubs.insert((group.callees, group.carried.clone()), hub);
                                }
                                hub
                            }
                        };
                        (group.node, group.site, group.via_drop, hub)
                    };
                    if hub != current[slot] {
                        current[slot] = hub;
                        if let Some(hub) = hub {
                            derivation.facts.push(RawFact {
                                from: node,
                                site,
                                via_drop,
                                hub,
                            });
                            changed = true;
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
        }
        let Derivation { hubs, facts, .. } = derivation;
        self.pools = pools;
        self.install(hubs, facts);
    }

    /// The part a hand-off of `carried` from `node` to `callee` derives to:
    /// a thread start itself (unless a RUN edge already makes that call), or
    /// what the callee's closure may invoke that `carried` admits, with the
    /// sinks of the open principals and unclosed pools it may reach.
    fn handoff_part(
        &mut self,
        derivation: &mut Derivation<'_>,
        context: &RoundContext<'_>,
        some: &mut SomeParts,
        node: ReachNode,
        callee: ReachNode,
        carried: &[CarriedKey],
    ) -> Option<usize> {
        let pools = derivation.pools;
        if self.is_seed(callee.index()) {
            // A hand-off to a thread start: the call that makes it is a RUN
            // edge, which outranks this one; without that edge the hand-off
            // is the only fact, and it is charged.
            if context.runs_into_seed.contains(&(node, callee)) {
                return None;
            }
            if let Some(part) = derivation.seed_parts.get(&callee) {
                return Some(*part);
            }
            let part = derivation.part(BTreeSet::from([callee]))?;
            derivation.seed_parts.insert(callee, part);
            return Some(part);
        }
        match context.summaries.of(callee.index()) {
            InvokedKeys::Every => {
                if let Some(part) = derivation.every.get(carried) {
                    return *part;
                }
                let mut targets: BTreeSet<ReachNode> = BTreeSet::new();
                for member in pools.members() {
                    if carried.iter().any(|carried| {
                        pools.admits(carried, &member.key) && pools.may_hold(carried, member)
                    }) {
                        targets.insert(member.member);
                    }
                }
                let open: BTreeSet<PrincipalKey> = pools
                    .open_principals()
                    .iter()
                    .copied()
                    .filter(|principal| {
                        carried
                            .iter()
                            .any(|carried| pools.admits_principal(carried, *principal))
                    })
                    .collect();
                let unenumerated = context.unclosed
                    && carried
                        .iter()
                        .any(|carried| pools.may_carry_callable(carried));
                for principal in open {
                    targets.insert(derivation.sink(&mut self.nodes, Some(principal)));
                }
                if unenumerated {
                    targets.insert(derivation.sink(&mut self.nodes, None));
                }
                let part = derivation.part(targets);
                derivation.every.insert(carried.to_vec(), part);
                part
            }
            // Only while the pools are closed: once they are not, every
            // invoke reaches the `UnclosedPool` sink, so a closure holding one
            // invokes `Every` key.
            InvokedKeys::Some(invoked) => {
                let component = context.summaries.component(callee.index());
                if let Some(part) = some.get(carried).and_then(|parts| parts.get(&component)) {
                    return *part;
                }
                let mut keys: BTreeSet<&PoolKey> = BTreeSet::new();
                for index in invoked {
                    keys.insert(&context.invokes[*index].key);
                }
                let mut targets: BTreeSet<ReachNode> = BTreeSet::new();
                let mut open: BTreeSet<PrincipalKey> = BTreeSet::new();
                for key in keys {
                    let admitting: Vec<&CarriedKey> = carried
                        .iter()
                        .filter(|carried| pools.admits(carried, key))
                        .collect();
                    if admitting.is_empty() {
                        continue;
                    }
                    targets.extend(
                        derivation
                            .lookup
                            .pool(pools, key)
                            .iter()
                            .map(|position| &pools.members()[*position])
                            .filter(|member| {
                                admitting
                                    .iter()
                                    .any(|carried| pools.may_hold(carried, member))
                            })
                            .map(|member| member.member),
                    );
                    if let Some(principal) = key.principal()
                        && pools.open_principals().contains(&principal)
                    {
                        open.insert(principal);
                    }
                }
                for principal in open {
                    targets.insert(derivation.sink(&mut self.nodes, Some(principal)));
                }
                let part = derivation.part(targets);
                some.entry(carried.to_vec())
                    .or_default()
                    .insert(component, part);
                part
            }
        }
    }

    /// Store the derivation: each hub becomes a node after every other node,
    /// with one APPROX edge from each fact's node to its hub (one per pair,
    /// as derivation keeps one edge per pair) and one from the hub to each
    /// target.
    fn install(&mut self, table: HubTable, raw: Vec<RawFact>) {
        let hub_base = self.nodes.len();
        let index = |value: usize| u32::try_from(value).unwrap_or(u32::MAX);
        self.nodes
            .extend(std::iter::repeat_n(ReachNodeKind::Hub, table.lists.len()));
        let mut derived = Derived {
            facts: Vec::with_capacity(raw.len()),
            hubs: table
                .lists
                .into_iter()
                .map(|targets| Hub {
                    targets,
                    facts: Vec::new(),
                    first_edge: 0,
                })
                .collect(),
            facts_from: vec![Vec::new(); hub_base],
            hubs_of: vec![Vec::new(); hub_base],
            hub_base,
        };
        let mut pairs: HashMap<(ReachNode, u32), u32> = HashMap::new();
        for (position, fact) in raw.into_iter().enumerate() {
            let hub_node = self.handle(hub_base + fact.hub as usize);
            let edge = match pairs.entry((fact.from, fact.hub)) {
                std::collections::hash_map::Entry::Vacant(slot) => {
                    let edge = index(self.edges.len());
                    self.edges.push(ReachEdge {
                        from: fact.from,
                        to: hub_node,
                        class: EdgeClass::Approx,
                        site: fact.site,
                        via_drop: fact.via_drop,
                    });
                    slot.insert(edge);
                    edge
                }
                std::collections::hash_map::Entry::Occupied(slot) => {
                    let edge = *slot.get();
                    let stored = &mut self.edges[edge as usize];
                    if stored.via_drop && !fact.via_drop {
                        stored.via_drop = false;
                        stored.site = fact.site;
                    }
                    edge
                }
            };
            derived.facts_from[fact.from.index()].push(index(position));
            derived.hubs[fact.hub as usize].facts.push(index(position));
            derived.facts.push(DerivedFact {
                from: fact.from,
                site: fact.site,
                via_drop: fact.via_drop,
                hub: fact.hub,
                edge,
            });
        }
        for (hub_index, hub) in derived.hubs.iter_mut().enumerate() {
            hub.first_edge = index(self.edges.len());
            let hub_node = self.handle(hub_base + hub_index);
            // A hub's edges have no site of their own: its first fact's.
            let site = hub
                .facts
                .first()
                .map_or(ReachSite::Mir(0), |fact| derived.facts[*fact as usize].site);
            for (position, target) in hub.targets.iter().enumerate() {
                self.edges.push(ReachEdge {
                    from: hub_node,
                    to: *target,
                    class: EdgeClass::Approx,
                    site,
                    via_drop: false,
                });
                derived.hubs_of[target.index()].push((index(hub_index), index(position)));
            }
        }
        self.derived = derived;
    }

    /// The four backward breadth-first reachabilities, and the labelling and
    /// certificate they give.
    ///
    /// The search is the one over the logical edges: a node's incoming edges
    /// are scanned adapter edges first, in order, then derived edges in
    /// derivation order. A hub costs nothing to pass: when the first of its
    /// targets is reached, the hub takes that target's distance and every
    /// fact naming it is scanned, merged with the other hubs that target
    /// fires, in fact order, so each node's distance and parent edge are
    /// those of the uncompressed search (a derived parent is the edge into
    /// the hub; [`ReachCensus::witness`] reads the hub's own parent after
    /// it). Ranks double the distance (a hub's is one more than its
    /// target's), so every justification still points strictly down.
    fn solve_levels(&self) -> (ReachCertificate, LevelParents) {
        let count = self.nodes.len();
        let adapter = &self.edges[..self.base_edges];
        // Incoming adapter edges, grouped by target (CSR).
        let mut starts = vec![0usize; count + 1];
        for edge in adapter {
            starts[edge.to.index() + 1] += 1;
        }
        for index in 0..count {
            starts[index + 1] += starts[index];
        }
        let mut fill = starts.clone();
        let mut incoming = vec![0u32; adapter.len()];
        for (index, edge) in adapter.iter().enumerate() {
            let slot = &mut fill[edge.to.index()];
            incoming[*slot] = u32::try_from(index).unwrap_or(u32::MAX);
            *slot += 1;
        }
        let derived = &self.derived;

        let mut distances: [Vec<u32>; 4] = std::array::from_fn(|_| vec![u32::MAX; count]);
        let mut parents: LevelParents = std::array::from_fn(|_| vec![NO_PARENT; count]);
        let mut merged: Vec<u32> = Vec::new();
        for (level_index, level) in Verdict::LEVELS.iter().enumerate() {
            let distance = &mut distances[level_index];
            let parent = &mut parents[level_index];
            let approx = EdgeClass::Approx.cap() >= *level;
            let mut fired = vec![false; derived.hubs.len()];
            let mut queue = VecDeque::new();
            for (node, slot) in distance.iter_mut().enumerate() {
                if self.is_seed(node) || (*level == Verdict::Unknown && self.is_sink(node)) {
                    *slot = 0;
                    queue.push_back(node);
                }
            }
            while let Some(node) = queue.pop_front() {
                for &edge_index in &incoming[starts[node]..starts[node + 1]] {
                    let edge = &self.edges[edge_index as usize];
                    let from = edge.from.index();
                    if edge.class.cap() >= *level && distance[from] == u32::MAX {
                        distance[from] = distance[node] + 1;
                        parent[from] = edge_index;
                        queue.push_back(from);
                    }
                }
                if !approx {
                    continue;
                }
                let Some(holders) = derived.hubs_of.get(node) else {
                    continue;
                };
                merged.clear();
                for &(hub, position) in holders {
                    if fired[hub as usize] {
                        continue;
                    }
                    fired[hub as usize] = true;
                    let hub_node = derived.hub_base + hub as usize;
                    distance[hub_node] = distance[node];
                    parent[hub_node] = derived.hubs[hub as usize].first_edge + position;
                    merged.extend_from_slice(&derived.hubs[hub as usize].facts);
                }
                // A fact names one hub, so the lists are disjoint.
                merged.sort_unstable();
                for &fact in &merged {
                    let fact = &derived.facts[fact as usize];
                    let from = fact.from.index();
                    if distance[from] == u32::MAX {
                        distance[from] = distance[node] + 1;
                        parent[from] = fact.edge;
                        queue.push_back(from);
                    }
                }
            }
        }

        let mut labels = vec![Verdict::Quiet; count];
        let mut justifications = vec![None; count];
        for node in 0..count {
            let Some(level_index) = (0..4).find(|level| distances[*level][node] != u32::MAX) else {
                continue;
            };
            labels[node] = Verdict::LEVELS[level_index];
            if self.base_label(node) != Some(labels[node]) {
                let hub = u32::from(self.is_hub_index(node));
                justifications[node] = Some(Justification {
                    rank: distances[level_index][node]
                        .saturating_mul(2)
                        .saturating_add(hub),
                    edge: parents[level_index][node],
                });
            }
        }
        let definitions = self.join_definitions(&labels);
        (
            ReachCertificate {
                labels,
                justifications,
                definitions,
            },
            parents,
        )
    }

    /// The per-definition join: the strongest label among a definition's nodes.
    fn join_definitions(&self, labels: &[Verdict]) -> Vec<(DefinitionKey, Verdict)> {
        let mut joined: BTreeMap<DefinitionKey, Verdict> = BTreeMap::new();
        for (node, kind) in self.nodes.iter().enumerate() {
            if let ReachNodeKind::Program(ReachNodeSpec {
                definition: Some(definition),
                ..
            }) = kind
            {
                let entry = joined.entry(*definition).or_insert(Verdict::Quiet);
                *entry = (*entry).max(labels[node]);
            }
        }
        joined.into_iter().collect()
    }
}

/// Lists each node's logical derived edges
/// ([`ExpandedReachGraph::derived_edge_scan`]), reusing its buffers.
pub struct DerivedEdgeScan<'graph> {
    graph: &'graph ExpandedReachGraph,
    stamp: Vec<u32>,
    slot: Vec<u32>,
    epoch: u32,
    edges: Vec<(DerivedOrder, ReachEdge)>,
}

impl DerivedEdgeScan<'_> {
    /// `from`'s logical derived edges in derivation order, each with its
    /// place in it and its final site and `via_drop` flag.
    pub fn edges_from(&mut self, from: ReachNode) -> &[(DerivedOrder, ReachEdge)] {
        self.edges.clear();
        let derived = &self.graph.derived;
        let Some(facts) = self
            .graph
            .local(from)
            .and_then(|index| derived.facts_from.get(index))
        else {
            return &self.edges;
        };
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.fill(0);
            self.epoch = 1;
        }
        for &fact_index in facts {
            let fact = &derived.facts[fact_index as usize];
            for (position, &to) in derived.hubs[fact.hub as usize].targets.iter().enumerate() {
                let target = to.index();
                if self.stamp[target] != self.epoch {
                    self.stamp[target] = self.epoch;
                    self.slot[target] = u32::try_from(self.edges.len()).unwrap_or(u32::MAX);
                    self.edges.push((
                        DerivedOrder {
                            fact: fact_index,
                            position: u32::try_from(position).unwrap_or(u32::MAX),
                        },
                        ReachEdge {
                            from,
                            to,
                            class: EdgeClass::Approx,
                            site: fact.site,
                            via_drop: fact.via_drop,
                        },
                    ));
                } else {
                    let edge = &mut self.edges[self.slot[target] as usize].1;
                    if edge.via_drop && !fact.via_drop {
                        edge.via_drop = false;
                        edge.site = fact.site;
                    }
                }
            }
        }
        &self.edges
    }
}

/// Why a labelled node carries its label: an admitted edge to a node whose
/// label is higher, or equal with a smaller rank. Ranks make the
/// justification well-founded, so a cycle cannot justify itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Justification {
    /// The solver's ranks are twice the search distance, and one more for a
    /// hub, which the search passes at its target's distance.
    pub rank: u32,
    /// Index into [`ExpandedReachGraph::edges`].
    pub edge: u32,
}

/// The verdict labelling of one expanded graph, as checkable data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReachCertificate {
    /// One label per node.
    pub labels: Vec<Verdict>,
    /// `Some` exactly for labelled nodes that are not a base (a seed labelled
    /// SPAWNS, a sink labelled UNKNOWN).
    pub justifications: Vec<Option<Justification>>,
    /// The per-definition join, sorted by key.
    pub definitions: Vec<(DefinitionKey, Verdict)>,
}

/// Why a certificate was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateError {
    /// The certificate does not have one entry per node.
    Shape,
    /// (i): a seed not labelled SPAWNS, a sink not labelled UNKNOWN, or a
    /// base given a justification.
    Base(ReachNode),
    /// (ii): an admitted edge whose source is labelled below its target.
    Unclosed { edge: usize },
    /// (iii): a labelled node without a well-founded admitted justification,
    /// or a QUIET node with one.
    Unjustified(ReachNode),
    /// The per-definition join differs from the labels.
    Definitions,
}

/// Re-verify a labelling of `graph` in O(V + E), plus an ordered map for the
/// per-definition join, without the solver's search (design 2026-09-29
/// §5.6, check 1, strengthened by ranks):
///
/// 1. every seed is SPAWNS and every sink UNKNOWN;
/// 2. on every edge `u → v`, `label(u) ≥ min(label(v), cap(class))`, so no
///    admitted edge leaves a lower label below a higher one;
/// 3. every other labelled node has an admitted edge to a node labelled
///    higher, or equal with a strictly smaller rank, so every label is
///    justified by a path to a base and no cycle justifies itself.
///
/// (2) makes the labels at least the least fixpoint and (3) at most, so an
/// accepted labelling IS the least fixpoint: any change to any label fails.
/// It is the least fixpoint OF `graph`: the engine-derived APPROX edges are
/// taken as given, so a pool or rule H edge the engine failed to derive is
/// invisible here (module docs).
pub fn check_reach_certificate(
    graph: &ExpandedReachGraph,
    certificate: &ReachCertificate,
) -> Result<(), CertificateError> {
    let count = graph.nodes.len();
    if certificate.labels.len() != count || certificate.justifications.len() != count {
        return Err(CertificateError::Shape);
    }
    let labels = &certificate.labels;
    for (index, (label, justification)) in
        labels.iter().zip(&certificate.justifications).enumerate()
    {
        if let Some(base) = graph.base_label(index)
            && (*label != base || justification.is_some())
        {
            return Err(CertificateError::Base(graph.handle(index)));
        }
    }
    for (index, edge) in graph.edges.iter().enumerate() {
        if labels[edge.from.index()] < labels[edge.to.index()].min(edge.class.cap()) {
            return Err(CertificateError::Unclosed { edge: index });
        }
    }
    let rank = |index: usize| match certificate.justifications[index] {
        Some(justification) => justification.rank,
        None if graph.base_label(index).is_some() => 0,
        None => u32::MAX,
    };
    for index in 0..count {
        if graph.base_label(index).is_some() {
            continue;
        }
        let label = labels[index];
        let justified = match (label, certificate.justifications[index]) {
            (Verdict::Quiet, None) => true,
            (Verdict::Quiet, Some(_)) | (_, None) => false,
            (label, Some(justification)) => graph
                .edges
                .get(justification.edge as usize)
                .is_some_and(|edge| {
                    let target = edge.to.index();
                    edge.from.index() == index
                        && edge.class.cap() >= label
                        && (labels[target] > label
                            || (labels[target] == label && rank(target) < justification.rank))
                }),
        };
        if !justified {
            return Err(CertificateError::Unjustified(graph.handle(index)));
        }
    }
    if graph.join_definitions(labels) != certificate.definitions {
        return Err(CertificateError::Definitions);
    }
    Ok(())
}

/// Why a census refused every node as UNKNOWN.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReachFallback {
    Defects(Vec<ReachDefect>),
    CertificateRejected(CertificateError),
}

/// A refusal's evidence: a shortest admitted path from the node to a seed (or,
/// for UNKNOWN, a sink), flagged when it runs a destructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReachWitness {
    pub verdict: Verdict,
    pub path: Vec<ReachEdge>,
    pub via_drop: bool,
}

/// A RUN or APPROX edge into a seed: a place a thread may start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SpawnSite {
    pub edge: ReachEdge,
    /// Where the new thread starts, when the adapter named the callable it
    /// runs: that callable, or a node that runs it together with the std code
    /// the thread runs around it (the trust-ir walk's, Trust design
    /// 2026-10-02, "C1", N-4). Its [`ReachCensus::thread_closure`] is what the
    /// new thread runs.
    pub entry: Option<ReachNode>,
}

/// What one thread runs: forward reach over RUN and APPROX edges from its
/// entry, never entering a seed (a spawn starts ANOTHER thread). The skeleton
/// of ty's thread model (design 2026-09-29 §4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThreadClosure {
    entry: Option<ReachNode>,
    /// Each reached node, with the edge that first reached it.
    reached: BTreeMap<ReachNode, Option<ReachEdge>>,
    modelable: bool,
}

impl ThreadClosure {
    #[must_use]
    pub fn entry(&self) -> Option<ReachNode> {
        self.entry
    }

    #[must_use]
    pub fn contains(&self, node: ReachNode) -> bool {
        self.reached.contains_key(&node)
    }

    pub fn nodes(&self) -> impl Iterator<Item = ReachNode> + '_ {
        self.reached.keys().copied()
    }

    /// A shortest path from the entry to `node`.
    #[must_use]
    pub fn path_to(&self, node: ReachNode) -> Option<Vec<ReachEdge>> {
        let mut path = Vec::new();
        let mut current = node;
        loop {
            match self.reached.get(&current)? {
                Some(edge) => {
                    path.push(*edge);
                    current = edge.from;
                }
                None => {
                    path.reverse();
                    return Some(path);
                }
            }
        }
    }

    /// R8: a model may be built only from a complete closure: a named entry,
    /// in a census that did not fall back, holding no UNKNOWN or INDIRECT
    /// node, no sink, no foreign (opaque) code whose effects are not
    /// enumerated, and no node with a PARAM edge, whose code the closure
    /// does not contain. A primitive's effects are enumerated by its checked
    /// summary, so it is admitted beside walked code and seeds (Trust design
    /// 2026-10-02, §3.2).
    #[must_use]
    pub fn modelable(&self) -> bool {
        self.modelable
    }
}

/// A solved census: verdicts, witnesses and thread closures over one lane.
#[derive(Debug)]
pub struct ReachCensus {
    graph: ExpandedReachGraph,
    certificate: ReachCertificate,
    parents: LevelParents,
    fallback: Option<ReachFallback>,
}

impl ReachCensus {
    fn adopt(
        mut graph: ExpandedReachGraph,
        (certificate, parents): (ReachCertificate, LevelParents),
    ) -> Self {
        if u32::try_from(graph.nodes.len()).is_err() {
            graph.defects.push(ReachDefect::TooLarge);
        }
        let fallback = if graph.defects.is_empty() {
            check_reach_certificate(&graph, &certificate)
                .err()
                .map(ReachFallback::CertificateRejected)
        } else {
            Some(ReachFallback::Defects(graph.defects.clone()))
        };
        Self {
            graph,
            certificate,
            parents,
            fallback,
        }
    }

    /// The facts the certificate is checked against.
    #[must_use]
    pub fn expanded(&self) -> &ExpandedReachGraph {
        &self.graph
    }

    /// The solver's labelling, for an independent re-check.
    #[must_use]
    pub fn certificate(&self) -> &ReachCertificate {
        &self.certificate
    }

    /// Why every node is UNKNOWN, if it is.
    #[must_use]
    pub fn fallback(&self) -> Option<&ReachFallback> {
        self.fallback.as_ref()
    }

    /// `node`'s verdict; UNKNOWN after a fallback and for a handle this
    /// census's graph did not issue.
    #[must_use]
    pub fn verdict(&self, node: ReachNode) -> Verdict {
        match self.graph.local(node) {
            Some(index) if self.fallback.is_none() => self.certificate.labels[index],
            Some(_) | None => Verdict::Unknown,
        }
    }

    /// The strongest verdict of a definition's nodes; `None` if no node has it.
    #[must_use]
    pub fn definition_verdict(&self, definition: DefinitionKey) -> Option<Verdict> {
        let index = self
            .certificate
            .definitions
            .binary_search_by_key(&definition, |(key, _)| *key)
            .ok()?;
        Some(if self.fallback.is_some() {
            Verdict::Unknown
        } else {
            self.certificate.definitions[index].1
        })
    }

    /// A shortest admitted path from `node` to the base of its verdict (a
    /// base's own path is empty), over the logical edges: a derived edge
    /// appears as itself, never as its hops through a hub. `None` for QUIET,
    /// after a fallback, for a hub and for a foreign handle.
    #[must_use]
    pub fn witness(&self, node: ReachNode) -> Option<ReachWitness> {
        let start = self.graph.local(node)?;
        let verdict = self.verdict(node);
        if self.fallback.is_some() || verdict == Verdict::Quiet || self.graph.is_hub_index(start) {
            return None;
        }
        let level = Verdict::LEVELS.iter().position(|level| *level == verdict)?;
        let parents = &self.parents[level];
        let mut path = Vec::new();
        let mut current = start;
        while parents[current] != NO_PARENT {
            let edge = self.graph.edges[parents[current] as usize];
            let edge = if self.graph.is_hub_index(edge.to.index()) {
                // Into a hub: the hub's own parent names the target the
                // search reached it from, and the logical edge is to that.
                let hub = edge.to.index();
                let target = self.graph.edges[parents[hub] as usize].to;
                self.graph.logical_edge(edge.from, target)?
            } else {
                edge
            };
            path.push(edge);
            current = edge.to.index();
        }
        let via_drop = path.iter().any(|edge| edge.via_drop);
        Some(ReachWitness {
            verdict,
            path,
            via_drop,
        })
    }

    /// Every logical RUN or APPROX edge into a seed, in order, with its
    /// named entry. `None` after a fallback: a malformed graph's sites are
    /// no enumeration, and an empty list would read as "no thread".
    #[must_use]
    pub fn spawn_sites(&self) -> Option<Vec<SpawnSite>> {
        if self.fallback.is_some() {
            return None;
        }
        let graph = &self.graph;
        let mut sites: Vec<SpawnSite> = graph.edges[..graph.base_edges]
            .iter()
            .enumerate()
            .filter(|(_, edge)| {
                matches!(edge.class, EdgeClass::Run | EdgeClass::Approx)
                    && graph.is_seed(edge.to.index())
            })
            .map(|(index, edge)| SpawnSite {
                edge: *edge,
                entry: graph.thread_entries.get(&index).copied().flatten(),
            })
            .collect();
        // Derived edges into a seed: each fact of a hub holding one, the
        // first per (node, seed) placing the edge.
        let mut derived: BTreeMap<(ReachNode, ReachNode), DerivedOrder> = BTreeMap::new();
        for (index, holders) in graph.derived.hubs_of.iter().enumerate() {
            if !graph.is_seed(index) {
                continue;
            }
            let seed = graph.handle(index);
            for &(hub, position) in holders {
                for &fact in &graph.derived.hubs[hub as usize].facts {
                    let order = DerivedOrder { fact, position };
                    let from = graph.derived.facts[fact as usize].from;
                    let slot = derived.entry((from, seed)).or_insert(order);
                    *slot = (*slot).min(order);
                }
            }
        }
        let mut derived: Vec<(DerivedOrder, ReachNode, ReachNode)> = derived
            .into_iter()
            .map(|((from, seed), order)| (order, from, seed))
            .collect();
        derived.sort_unstable_by_key(|(order, _, _)| *order);
        for (_, from, seed) in derived {
            sites.push(SpawnSite {
                edge: graph.logical_edge(from, seed)?,
                entry: None,
            });
        }
        Some(sites)
    }

    /// What the thread entered at `entry` runs, over the logical edges (`None`,
    /// a foreign handle, or a hub: an unnamed entry, never modelable).
    #[must_use]
    pub fn thread_closure(&self, entry: Option<ReachNode>) -> ThreadClosure {
        let graph = &self.graph;
        let mut reached: BTreeMap<ReachNode, Option<ReachEdge>> = BTreeMap::new();
        let Some(start) = entry.filter(|node| {
            graph
                .local(*node)
                .is_some_and(|index| !graph.is_hub_index(index))
        }) else {
            return ThreadClosure {
                entry,
                reached,
                modelable: false,
            };
        };
        let count = graph.nodes.len();
        let mut outgoing: Vec<Vec<usize>> = vec![Vec::new(); count];
        let mut param = vec![false; count];
        for (index, edge) in graph.edges[..graph.base_edges].iter().enumerate() {
            match edge.class {
                EdgeClass::Run | EdgeClass::Approx => outgoing[edge.from.index()].push(index),
                EdgeClass::Param => param[edge.from.index()] = true,
                EdgeClass::Create | EdgeClass::Read => {}
            }
        }
        // A hub whose targets are all reached adds nothing to a later fact.
        let mut spent = vec![false; graph.derived.hubs.len()];
        reached.insert(start, None);
        let mut queue = VecDeque::from([start]);
        while let Some(node) = queue.pop_front() {
            if graph.is_seed(node.index()) {
                continue;
            }
            for &index in &outgoing[node.index()] {
                let edge = graph.edges[index];
                if let std::collections::btree_map::Entry::Vacant(slot) = reached.entry(edge.to) {
                    slot.insert(Some(edge));
                    queue.push_back(edge.to);
                }
            }
            // Then its derived edges, in derivation order.
            let Some(facts) = graph.derived.facts_from.get(node.index()) else {
                continue;
            };
            for &fact in facts {
                let hub = graph.derived.facts[fact as usize].hub as usize;
                if spent[hub] {
                    continue;
                }
                spent[hub] = true;
                for &target in &graph.derived.hubs[hub].targets {
                    if reached.contains_key(&target) {
                        continue;
                    }
                    let Some(edge) = graph.logical_edge(node, target) else {
                        continue;
                    };
                    reached.insert(target, Some(edge));
                    queue.push_back(target);
                }
            }
        }
        let modelable = self.fallback.is_none()
            && reached.keys().all(|node| {
                let index = node.index();
                !param[index]
                    && !matches!(self.verdict(*node), Verdict::Unknown | Verdict::Indirect)
                    && matches!(
                        graph.nodes[index],
                        ReachNodeKind::Program(ReachNodeSpec {
                            body: NodeBody::Walked | NodeBody::Seed | NodeBody::Primitive,
                            ..
                        })
                    )
            });
        ThreadClosure {
            entry,
            reached,
            modelable,
        }
    }
}

// ===========================================================================
// The trust-ir adapter's walk (design 2026-09-29 §5.2)
// ===========================================================================

/// How [`inspect_module_reachability`] treats a function it reaches. The
/// classifier sees what the module does not carry (trustc's callee ledger and
/// diagnostic items); absent is never quiet, so every class but `Walk`,
/// `Seed` and `Primitive` is either opaque by a disclosed policy or UNKNOWN.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionClass {
    /// Walk the stored body (a bodyless one is UNKNOWN).
    Walk,
    /// Walk the stored body, which is ALSO UNKNOWN(`ElidedDrops`): the
    /// producer elided its drops.
    WalkDropsElided,
    /// A thread-creation entry point; `spawned` is the callable this
    /// declaration's instance starts, when the classifier can name it.
    /// `child` is the checked summary of the std code the new thread runs
    /// around `spawned` (Trust design 2026-10-02, "C1", N-4): inherited spawn
    /// hooks before it; the result store, the drop glue of its result and the
    /// payload's drop slot after it; thread-local destructors. The thread
    /// starts at a node ([`NodeOrigin::TrustIrThreadStart`]) that runs
    /// `spawned` and carries `child`'s facts as a primitive's, so the thread's
    /// closure holds that code. Nothing reaches that node, so no caller's
    /// verdict reads it; its facts are otherwise ordinary ones, and a sink
    /// among them (an unresolved glue type, say) leaves the pools unclosed as
    /// any sink does. `None` is not enumerated: the node is then opaque, with
    /// no fact but its RUN of `spawned`, and the thread is never modelable.
    Seed {
        spawned: Option<FuncId>,
        child: Option<PrimitiveSummary>,
    },
    /// A thread primitive (`thread::scope`, the two `join`s; Trust design
    /// 2026-10-02, "C1", §3.2): its stored body, if any, is not walked. The
    /// node's facts are its summary's, each the fact the instruction doing it
    /// adds in a walked body. R9 is the premise: the primitive's own code
    /// starts no thread and leaves only through the facts its summary lists.
    /// A summary is evidence only as far as the classifier's pin establishes
    /// that premise.
    Primitive(PrimitiveSummary),
    /// A foreign symbol resolved by link name to a module function (the
    /// allocator shim to the `#[global_allocator]`, say): a RUN edge to it.
    LinkResolved(FuncId),
    /// Foreign (C) code: opaque, assumed to start no thread itself (R3), and
    /// charged by rule H with what callers hand it.
    Foreign,
    /// A havoc declaration standing for a call through the caller's own type
    /// parameters: a PARAM edge (R1).
    CallerTypeParameter,
    /// Not enumerated.
    Unknown(DependencyRefusalKind),
}

/// The facts a primitive's own code leaves through (R9; Trust design
/// 2026-10-02, "C1", §3.2), or the std code a seed's new thread runs around
/// its callable (N-4, `FunctionClass::Seed::child`). Each item becomes the
/// fact the instruction that does it adds in a walked body, at the
/// primitive's (the seed's) definition site. An empty summary claims the code
/// does nothing the census can see.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PrimitiveSummary {
    /// Callbacks it runs on the thread that runs it: each is RUN, as a
    /// `Call`.
    pub runs: Vec<FuncId>,
    /// Runtime services it uses, such as the panic service, each classified
    /// as an instruction's ([`DeclClassifier::runtime_service`]).
    pub services: Vec<RuntimeService>,
    /// Indirect calls it makes: a pool INVOKE of each, such as the drop slot
    /// of `dyn Any + Send`.
    pub invokes: Vec<PrimitiveInvoke>,
    /// Types whose drop glue it runs, each as a `Drop` of that type: its
    /// glue when the drop-glue table resolves it, else
    /// UNKNOWN(`ImplicitDestructor`), via drop either way.
    pub glue: Vec<Ty>,
}

/// One indirect call in a [`PrimitiveSummary`]: the pool key it is charged
/// by, and what its operands carry. A member of that pool that is external
/// code is handed what `carried` admits, and the primitive is charged with it
/// by rule H, as a walked body's `CallIndirect` is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrimitiveInvoke {
    pub key: PoolKey,
    pub carried: Vec<CarriedKey>,
}

/// What a [`RuntimeService`] runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ServiceClass {
    /// A RUN edge to this module function.
    Resolved(FuncId),
    /// Foreign runtime code, assumed to start no thread (R3).
    Foreign,
    /// Not enumerated.
    Unknown(DependencyRefusalKind),
}

/// The source knowledge the trust-ir walk needs and the module lacks.
pub trait DeclClassifier {
    /// How to treat `function`; asked once per function.
    fn classify(&self, function: &Function) -> FunctionClass;
    /// The definition `function`'s verdict joins into.
    fn definition(&self, function: &Function) -> DefinitionKey;
    /// What `service` runs; asked once per service.
    fn runtime_service(&self, service: RuntimeService) -> ServiceClass;
}

/// The trust-ir lane's census of one module.
#[derive(Debug)]
pub struct ModuleReachability<'module> {
    module: &'module Module,
    census: ReachCensus,
    nodes: BTreeMap<DependencyNode, ReachNode>,
}

impl<'module> ModuleReachability<'module> {
    #[must_use]
    pub fn module(&self) -> &'module Module {
        self.module
    }

    #[must_use]
    pub fn census(&self) -> &ReachCensus {
        &self.census
    }

    /// The node of a function or global id the module holds or names.
    #[must_use]
    pub fn node(&self, node: DependencyNode) -> Option<ReachNode> {
        self.nodes.get(&node).copied()
    }

    /// A function's verdict. Every function of the module has one (an id two
    /// definitions share is one UNKNOWN node); `None` means the module holds
    /// no function of that id: never read it as QUIET.
    #[must_use]
    pub fn function_verdict(&self, function: FuncId) -> Option<Verdict> {
        self.node(DependencyNode::Function(function))
            .map(|node| self.census.verdict(node))
    }
}

/// The trust-ir adapter's walk (design 2026-09-29 §5.2): the census of EVERY
/// function and global of the module, so its pools hold every CREATE the
/// module states and no root set can leave one out.
///
/// It is a second walk beside [`inspect_function_dependencies`], and shares
/// with it the module lookups (function ids, link-time symbols, the
/// module-level refusals), the body-shape refusals, the exhaustive
/// instruction and constant matches, and the exact indirect-call check. Like
/// it, it borrows the module, scans every stored block of every walked body
/// (so a const-false branch is still walked, j05), and has no cutoff. Unlike
/// it, it does not walk types, which name no code: a missing or opaque type
/// widens a pool key or a rule H carrier instead of refusing.
///
/// | trust-ir | census |
/// |---|---|
/// | `Call` / `Invoke` / `SeqMap` to a body | RUN |
/// | `Call` to a bodyless declaration | by [`FunctionClass`] |
/// | a function the classifier calls a primitive | RUN to it; its summary's facts, at its definition |
/// | a call of a seed | RUN to it, a spawn site; its thread starts at one node per seed that RUNs the spawned callable and carries the seed's child summary's facts (opaque without one) |
/// | `CallIndirect` | exact (RUN), else its FnPool, else UNKNOWN |
/// | `Drop` / `DropInvoke` | RUN to its glue (via drop) when resolved through the drop-glue table; UNKNOWN(`ImplicitDestructor`) when unresolved |
/// | `Const{FnDef \| Closure}`, function `SymbolAddr` | CREATE and pool member |
/// | `GlobalAddr`, global `SymbolAddr` | READ of the global's initializer |
/// | `Cast` changing a callable-carrying type | LAUNDER |
/// | `Assert`, `HeapAlloc`, `Dealloc`, `Retain`/`Release`/`IsUnique` | by [`ServiceClass`] |
/// | `DialectOp`, global assembly | UNKNOWN |
/// | a function id two definitions share | one node, UNKNOWN(`Ambiguous`) |
///
/// Every member is non-confined here (confinement is not computed on this
/// lane, which only widens pools), FnPool shapes state no convention
/// ([`FnShape::abi`]), and `dyn` dispatch reaches the classifier as a havoc
/// declaration until vtables carry their methods. Any UNKNOWN sink leaves the
/// pools unclosed, so while drops are refused nearly every indirect call on
/// this lane is UNKNOWN.
pub fn inspect_module_reachability<'module>(
    module: &'module Module,
    classifier: &dyn DeclClassifier,
) -> ModuleReachability<'module> {
    let walker = ReachWalker::walk(module, classifier);
    ModuleReachability {
        module,
        census: walker.graph.solve(),
        nodes: walker.nodes,
    }
}

impl<'module, 'classifier> ReachWalker<'module, 'classifier> {
    /// Every function and global of `module`, and everything they reach.
    fn walk(module: &'module Module, classifier: &'classifier dyn DeclClassifier) -> Self {
        let mut walker = ReachWalker {
            module,
            classifier,
            index: ModuleIndex::new(module),
            nominal: module.nominal_type_reachability(),
            graph: ReachGraph::new(),
            nodes: BTreeMap::new(),
            classes: BTreeMap::new(),
            services: HashMap::new(),
            pending: VecDeque::new(),
            thread_starts: BTreeMap::new(),
            carries: SignatureCarries::default(),
        };
        for function in &module.functions {
            // Every id the module holds gets a node, an ambiguous one included.
            let _ = walker.function_node(function.id);
        }
        for position in 0..module.globals.len() {
            // A global past `u32` is refused module-wide (GlobalTableTooLarge).
            if let Ok(id) = u32::try_from(position) {
                let _ = walker.global_node(GlobalId(id));
            }
        }
        while let Some(node) = walker.pending.pop_front() {
            walker.expand(node);
        }
        walker
    }
}

struct ReachWalker<'module, 'classifier> {
    module: &'module Module,
    classifier: &'classifier dyn DeclClassifier,
    index: ModuleIndex<'module>,
    nominal: NominalTypeReachability<'module>,
    graph: ReachGraph,
    nodes: BTreeMap<DependencyNode, ReachNode>,
    classes: BTreeMap<FuncId, FunctionClass>,
    services: HashMap<RuntimeService, ServiceClass>,
    pending: VecDeque<DependencyNode>,
    /// Each seed's thread-start node ([`Self::thread_start`]).
    thread_starts: BTreeMap<FuncId, ReachNode>,
    /// The rule H keys of each signature's arguments
    /// ([`Self::signature_carries`]).
    carries: SignatureCarries,
}

/// The rule H keys a signature's arguments carry, decided once per signature
/// for the pass, over one all-definitions index: a foreign or indirect call
/// site costs a lookup, not a walk of its signature's types (each of which
/// once scanned the definition list at every named type it met, then built a
/// hash index of the whole table per call).
#[derive(Default)]
struct SignatureCarries {
    defs: crate::reach::DefIndex,
    keys: HashMap<FuncTyId, Vec<CarriedKey>>,
    /// Signatures walked: one per distinct signature asked.
    walks: usize,
}

impl<'module> ReachWalker<'module, '_> {
    /// The node of function `id`. An id two definitions share is one node
    /// standing for all of them, UNKNOWN(`Ambiguous`): their bodies are not
    /// walked. A missing id has no node: the referring fact is UNKNOWN.
    fn function_node(&mut self, id: FuncId) -> Result<ReachNode, DependencyRefusalKind> {
        let key = DependencyNode::Function(id);
        if let Some(node) = self.nodes.get(&key) {
            return Ok(*node);
        }
        let (class, definition) = match self.index.function(id) {
            Ok(function) => (
                self.classifier.classify(function),
                Some(self.classifier.definition(function)),
            ),
            Err(reason @ DependencyRefusalKind::Ambiguous(_)) => {
                (FunctionClass::Unknown(reason), None)
            }
            Err(reason) => return Err(reason),
        };
        let (locality, body) = match &class {
            FunctionClass::Walk
            | FunctionClass::WalkDropsElided
            | FunctionClass::LinkResolved(_) => (Locality::Local, NodeBody::Walked),
            FunctionClass::Seed { .. } => (Locality::External, NodeBody::Seed),
            // The locality of the walked body it stands for: on this lane
            // every walked function is local, so rule H charges a callable
            // the primitive's invoke hands to external code, as it would the
            // twin's indirect call.
            FunctionClass::Primitive(_) => (Locality::Local, NodeBody::Primitive),
            FunctionClass::Foreign => (Locality::External, NodeBody::Opaque),
            FunctionClass::CallerTypeParameter => (Locality::External, NodeBody::Param),
            FunctionClass::Unknown(_) => (Locality::External, NodeBody::Walked),
        };
        let node = self.graph.add_node(ReachNodeSpec {
            origin: NodeOrigin::TrustIr(key),
            definition,
            locality,
            body,
        });
        self.nodes.insert(key, node);
        self.classes.insert(id, class);
        self.pending.push_back(key);
        Ok(node)
    }

    fn global_node(&mut self, id: GlobalId) -> Result<ReachNode, DependencyRefusalKind> {
        let key = DependencyNode::Global(id);
        if let Some(node) = self.nodes.get(&key) {
            return Ok(*node);
        }
        if self.module.globals.get(id.as_usize()).is_none() {
            return Err(DependencyRefusalKind::Missing(key));
        }
        let node = self.graph.add_node(ReachNodeSpec {
            origin: NodeOrigin::TrustIr(key),
            definition: None,
            locality: Locality::Local,
            body: NodeBody::Walked,
        });
        self.nodes.insert(key, node);
        self.pending.push_back(key);
        Ok(node)
    }

    fn unknown(
        &mut self,
        from: ReachNode,
        reason: DependencyRefusalKind,
        class: EdgeClass,
        site: ReachSite,
    ) {
        self.graph.add_unknown(from, reason, class, site, false);
    }

    fn expand(&mut self, key: DependencyNode) {
        let node = self.nodes[&key];
        let site = ReachSite::TrustIr(DependencySite::Definition(key));
        match key {
            DependencyNode::Function(id) => {
                let class = self.classes[&id].clone();
                if !matches!(class, FunctionClass::Seed { .. }) {
                    let module_site = ReachSite::TrustIr(DependencySite::Module);
                    for refusal in self.index.module_refusals(self.module) {
                        self.unknown(node, refusal, EdgeClass::Run, module_site);
                    }
                }
                match class {
                    FunctionClass::Walk => self.body(node, id),
                    FunctionClass::WalkDropsElided => {
                        self.graph.add_unknown(
                            node,
                            DependencyRefusalKind::ElidedDrops,
                            EdgeClass::Run,
                            site,
                            true,
                        );
                        self.body(node, id);
                    }
                    FunctionClass::LinkResolved(target) => self.call(node, target, site),
                    FunctionClass::Primitive(summary) => self.primitive(node, &summary, site),
                    FunctionClass::Unknown(reason) => {
                        self.unknown(node, reason, EdgeClass::Run, site)
                    }
                    FunctionClass::Seed { .. }
                    | FunctionClass::Foreign
                    | FunctionClass::CallerTypeParameter => {}
                }
            }
            DependencyNode::Global(id) => match &self.module.globals[id.as_usize()].initializer {
                Some(value) => self.constant(node, value, None, site),
                None => self.unknown(
                    node,
                    DependencyRefusalKind::MissingGlobalInitializer(id),
                    EdgeClass::Read,
                    site,
                ),
            },
            // Only functions and globals become reach nodes.
            DependencyNode::Type(_)
            | DependencyNode::FunctionType(_)
            | DependencyNode::Struct(_)
            | DependencyNode::Enum(_)
            | DependencyNode::Record(_)
            | DependencyNode::ClosureType(_)
            | DependencyNode::Predicate(_)
            | DependencyNode::Universe(_) => {}
        }
    }

    /// A RUN edge to `callee`, shaped by its class.
    fn call(&mut self, from: ReachNode, callee: FuncId, site: ReachSite) {
        self.call_via(from, callee, site, false);
    }

    /// [`Self::call`], with every fact it adds flagged `via_drop` (a
    /// resolved drop's call of its glue, amendment D).
    fn call_via(&mut self, from: ReachNode, callee: FuncId, site: ReachSite, via_drop: bool) {
        let node = match self.function_node(callee) {
            Ok(node) => node,
            Err(reason) => {
                self.graph
                    .add_unknown(from, reason, EdgeClass::Run, site, via_drop);
                return;
            }
        };
        match self.classes[&callee].clone() {
            FunctionClass::Seed { spawned, child } => {
                let entry =
                    spawned.and_then(|spawned| self.thread_start(callee, spawned, child.as_ref()));
                self.graph.add_spawn(from, node, entry, site, via_drop);
            }
            FunctionClass::CallerTypeParameter => {
                self.graph
                    .add_edge(from, node, EdgeClass::Param, site, via_drop)
            }
            FunctionClass::Foreign => {
                self.graph
                    .add_edge(from, node, EdgeClass::Run, site, via_drop);
                let signature = self.index.function(callee).ok().map(|callee| callee.ty);
                let carried = self.signature_carries(signature);
                self.graph.add_handoff(from, node, carried, site, via_drop);
            }
            FunctionClass::Walk
            | FunctionClass::WalkDropsElided
            | FunctionClass::LinkResolved(_)
            | FunctionClass::Primitive(_)
            | FunctionClass::Unknown(_) => {
                self.graph
                    .add_edge(from, node, EdgeClass::Run, site, via_drop)
            }
        }
    }

    /// Where the thread a call of `seed` starts begins (Trust design
    /// 2026-10-02, "C1", N-4): one node per seed declaration, which runs
    /// `spawned` and carries `child`'s facts as a primitive's
    /// ([`Self::primitive`]), at the seed's definition. It is local, as a
    /// primitive is on this lane. Without a summary it is opaque: the std code
    /// it stands for is not enumerated, so no closure through it is
    /// modelable, and it adds no sink, so no verdict moves. `None` when
    /// `spawned` is no function of the module: the entry is unnamed.
    /// Nothing reaches the node; only [`ReachCensus::thread_closure`] of a
    /// spawn site's entry reads it.
    fn thread_start(
        &mut self,
        seed: FuncId,
        spawned: FuncId,
        child: Option<&PrimitiveSummary>,
    ) -> Option<ReachNode> {
        if let Some(start) = self.thread_starts.get(&seed) {
            return Some(*start);
        }
        let entry = self.function_node(spawned).ok()?;
        let start = self.graph.add_node(ReachNodeSpec {
            origin: NodeOrigin::TrustIrThreadStart(seed),
            definition: None,
            locality: Locality::Local,
            body: if child.is_some() {
                NodeBody::Primitive
            } else {
                NodeBody::Opaque
            },
        });
        self.thread_starts.insert(seed, start);
        let site = ReachSite::TrustIr(DependencySite::Definition(DependencyNode::Function(seed)));
        self.graph
            .add_edge(start, entry, EdgeClass::Run, site, false);
        if let Some(child) = child {
            self.primitive(start, child, site);
        }
        Some(start)
    }

    /// The rule H keys a signature's arguments carry. An unknown signature,
    /// and a C-variadic one (its extra arguments have no stated type), may
    /// carry anything. Decided once per signature for the pass
    /// ([`SignatureCarries`]).
    fn signature_carries(&mut self, signature: Option<FuncTyId>) -> Vec<CarriedKey> {
        let Some((id, signature)) =
            signature.and_then(|id| Some((id, self.module.func_types.get(id.as_usize())?)))
        else {
            return vec![CarriedKey::Any];
        };
        if signature.is_vararg {
            return vec![CarriedKey::Any];
        }
        if let Some(keys) = self.carries.keys.get(&id) {
            return keys.clone();
        }
        let module = self.module;
        let SignatureCarries { defs, keys, walks } = &mut self.carries;
        *walks += 1;
        let mut carried: Vec<CarriedKey> = signature
            .params
            .iter()
            .flat_map(|ty| carried_keys(module, defs, ty))
            .collect();
        carried.sort();
        carried.dedup();
        keys.insert(id, carried.clone());
        carried
    }

    /// `from` makes `target` a callable value of `shape`.
    fn create(&mut self, from: ReachNode, target: FuncId, shape: FnShape, site: ReachSite) {
        match self.function_node(target) {
            Ok(node) if self.classes[&target] == FunctionClass::CallerTypeParameter => self
                .graph
                .add_edge(from, node, EdgeClass::Param, site, false),
            Ok(node) => self
                .graph
                .add_create(from, node, PoolKey::Fn(shape), false, site),
            Err(reason) => self.unknown(from, reason, EdgeClass::Create, site),
        }
    }

    fn function_shape(&self, function: FuncId) -> FnShape {
        match self.index.function(function) {
            Ok(function) => fn_pool_shape(self.module, function.ty),
            Err(_) => FnShape::unclassified(),
        }
    }

    /// Every callable a constant names. A top-level closure's shape comes from
    /// its stated closure type; a nested one's is unclassified.
    fn constant(
        &mut self,
        from: ReachNode,
        value: &'module Constant,
        ty: Option<&Ty>,
        site: ReachSite,
    ) {
        let top_closure_shape = match ty {
            Some(Ty::Closure(closure)) => self
                .module
                .closure_types
                .get(closure.as_usize())
                .map(|closure| fn_pool_shape(self.module, closure.func)),
            _ => None,
        };
        value.visit_constants(|constant| match constant_reach(constant) {
            ConstantReach::Function(function) => {
                let shape = self.function_shape(function);
                self.create(from, function, shape, site);
            }
            ConstantReach::Closure(function) => {
                let shape = match (&top_closure_shape, std::ptr::eq(constant, value)) {
                    (Some(shape), true) => shape.clone(),
                    _ => FnShape::unclassified(),
                };
                self.create(from, function, shape, site);
            }
            ConstantReach::Symbol(symbol) => match self.index.symbols.resolve(symbol) {
                Ok(DependencyNode::Function(function)) => {
                    let shape = self.function_shape(function);
                    self.create(from, function, shape, site);
                }
                Ok(DependencyNode::Global(global)) => match self.global_node(global) {
                    Ok(node) => self
                        .graph
                        .add_edge(from, node, EdgeClass::Read, site, false),
                    Err(reason) => self.unknown(from, reason, EdgeClass::Read, site),
                },
                // The symbol table holds only functions and globals.
                Ok(other) => self.unknown(
                    from,
                    DependencyRefusalKind::Missing(other),
                    EdgeClass::Create,
                    site,
                ),
                Err(reason) => self.unknown(from, reason, EdgeClass::Create, site),
            },
            ConstantReach::Nothing => {}
        });
    }

    /// A use of `service`, as its class says.
    fn service(&mut self, node: ReachNode, service: RuntimeService, site: ReachSite) {
        let class = self
            .services
            .entry(service)
            .or_insert_with(|| self.classifier.runtime_service(service))
            .clone();
        match class {
            ServiceClass::Resolved(target) => self.call(node, target, site),
            ServiceClass::Foreign => {}
            ServiceClass::Unknown(reason) => self.unknown(node, reason, EdgeClass::Run, site),
        }
    }

    /// A primitive's facts, from its checked summary: each item is the fact
    /// the instruction doing it adds in a walked body ([`Self::body`]), at the
    /// primitive's definition site.
    fn primitive(&mut self, node: ReachNode, summary: &PrimitiveSummary, site: ReachSite) {
        for callback in &summary.runs {
            self.call(node, *callback, site);
        }
        for service in &summary.services {
            self.service(node, *service, site);
        }
        for invoke in &summary.invokes {
            self.graph.add_invoke(
                node,
                invoke.key.clone(),
                invoke.carried.clone(),
                site,
                false,
            );
        }
        // As `instruction_reach` resolves a `Drop`, and `body` adds its fact.
        for ty in &summary.glue {
            match self.index.drop_glue.resolve(ty) {
                crate::DropResolution::Resolved(glue) => self.call_via(node, glue, site, true),
                crate::DropResolution::Unresolved | crate::DropResolution::Ambiguous => {
                    self.graph.add_unknown(
                        node,
                        DependencyRefusalKind::ImplicitDestructor(ty.clone()),
                        EdgeClass::Run,
                        site,
                        true,
                    );
                }
            }
        }
    }

    fn body(&mut self, node: ReachNode, id: FuncId) {
        let Ok(function) = self.index.function(id) else {
            return;
        };
        let site = ReachSite::TrustIr(DependencySite::Definition(DependencyNode::Function(id)));
        for refusal in body_shape_refusals(function) {
            self.unknown(node, refusal, EdgeClass::Run, site);
        }
        let pointers = StaticFunctionPointerAnalysis::new(function);
        for block in &function.blocks {
            for (index, instruction) in block.body.iter().enumerate() {
                let site = ReachSite::TrustIr(DependencySite::Instruction {
                    function: id,
                    block: block.id,
                    index,
                });
                match instruction_reach(&instruction.inst, &self.index.drop_glue) {
                    InstructionReach::Call(callee) | InstructionReach::SeqMap(callee) => {
                        self.call(node, callee, site)
                    }
                    // Amendment D: a resolved drop runs its glue — an edge
                    // that exists THROUGH a drop.
                    InstructionReach::DropGlue(glue) => self.call_via(node, glue, site, true),
                    InstructionReach::Indirect {
                        callee,
                        sig,
                        calling_conv,
                    } => {
                        if let Some(resolution) = pointers.resolve_typed_at(callee, block.id, index)
                        {
                            self.call(node, resolution.function(), site);
                            if !exact_indirect_target(
                                &self.index.functions,
                                &resolution,
                                sig,
                                calling_conv,
                            ) {
                                self.unknown(
                                    node,
                                    DependencyRefusalKind::IndirectSignatureMismatch,
                                    EdgeClass::Run,
                                    site,
                                );
                            }
                        } else if self.module.func_types.get(sig.as_usize()).is_none() {
                            self.unknown(
                                node,
                                DependencyRefusalKind::Missing(DependencyNode::FunctionType(sig)),
                                EdgeClass::Run,
                                site,
                            );
                        } else {
                            let key = PoolKey::Fn(fn_pool_shape(self.module, sig));
                            let carried = self.signature_carries(Some(sig));
                            self.graph.add_invoke(node, key, carried, site, false);
                        }
                    }
                    InstructionReach::Global(global) => match self.global_node(global) {
                        Ok(target) => {
                            self.graph
                                .add_edge(node, target, EdgeClass::Read, site, false)
                        }
                        Err(reason) => self.unknown(node, reason, EdgeClass::Read, site),
                    },
                    // Amendment P: a failed sited check RUNS its entry and
                    // passes its location global's address.
                    InstructionReach::PanicSite { entry, global } => {
                        self.call(node, entry, site);
                        if let Some(global) = global {
                            match self.global_node(global) {
                                Ok(target) => {
                                    self.graph
                                        .add_edge(node, target, EdgeClass::Read, site, false)
                                }
                                Err(reason) => self.unknown(node, reason, EdgeClass::Read, site),
                            }
                        }
                    }
                    InstructionReach::Constant(value, ty) => {
                        self.constant(node, value, Some(ty), site)
                    }
                    InstructionReach::Closure(ty, func) => {
                        let shape = self
                            .module
                            .closure_types
                            .get(ty.as_usize())
                            .map(|closure| fn_pool_shape(self.module, closure.func))
                            .unwrap_or_else(FnShape::unclassified);
                        self.create(node, func, shape, site);
                    }
                    InstructionReach::Cases(cases) => {
                        for case in cases {
                            self.constant(node, &case.value, None, site);
                        }
                    }
                    InstructionReach::Drop(ty) => {
                        self.graph.add_unknown(
                            node,
                            DependencyRefusalKind::ImplicitDestructor(ty.clone()),
                            EdgeClass::Run,
                            site,
                            true,
                        );
                    }
                    InstructionReach::Opaque => self.unknown(
                        node,
                        DependencyRefusalKind::OpaqueDialectOperation,
                        EdgeClass::Run,
                        site,
                    ),
                    InstructionReach::Cast { op, src, dst } => {
                        if cast_launders(&self.nominal, op, src, dst) {
                            self.graph.add_launder(site);
                        }
                    }
                    InstructionReach::Runtime(service) => self.service(node, service, site),
                    InstructionReach::Nothing => {}
                }
            }
        }
    }
}

#[cfg(test)]
mod reference;

/// The compressed derivation against the uncompressed one it replaces
/// (`reference`), on random fact graphs: the same nodes in the same order
/// (engine sinks included, hubs after them), the same logical edges in the
/// same order with the same sites and flags, and the same labels,
/// definitions, witnesses, spawn sites and thread closures.
#[cfg(test)]
mod compressed_derivation_tests {
    use super::reference::Reference;
    use super::*;
    use crate::analysis::{ArgClass, MethodKey};

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, bound: usize) -> usize {
            (self.next() % bound as u64) as usize
        }

        fn chance(&mut self, percent: u64) -> bool {
            self.next() % 100 < percent
        }
    }

    fn fn_key(params: Option<Vec<ArgClass>>) -> PoolKey {
        PoolKey::Fn(FnShape {
            abi: Some(0),
            variadic: Some(false),
            params,
        })
    }

    fn keys() -> Vec<PoolKey> {
        vec![
            fn_key(Some(vec![])),
            fn_key(Some(vec![ArgClass::Int(32)])),
            fn_key(Some(vec![ArgClass::Unclassified])),
            fn_key(Some(vec![ArgClass::Int(64)])),
            fn_key(None),
            PoolKey::Fn(FnShape::unclassified()),
            PoolKey::DynMethod {
                principal: PrincipalKey(1),
                method: MethodKey(1),
            },
            PoolKey::DynMethod {
                principal: PrincipalKey(1),
                method: MethodKey(2),
            },
            PoolKey::DynMethod {
                principal: PrincipalKey(2),
                method: MethodKey(1),
            },
            PoolKey::DynMethod {
                principal: PrincipalKey(3),
                method: MethodKey(1),
            },
            PoolKey::DynDrop(PrincipalKey(1)),
            PoolKey::DynDrop(PrincipalKey(2)),
            PoolKey::DynDrop(PrincipalKey(3)),
        ]
    }

    fn carried(rng: &mut Rng, keys: &[PoolKey], principals: u64) -> Vec<CarriedKey> {
        let mut out = Vec::new();
        for _ in 0..rng.below(3) {
            out.push(match rng.below(8) {
                0 => CarriedKey::AnyFn,
                1 => CarriedKey::AnyDyn,
                2 => CarriedKey::Any,
                3 => CarriedKey::Laundered,
                7 => CarriedKey::Untyped,
                4 => CarriedKey::Principal(PrincipalKey(1 + rng.next() % principals)),
                _ => CarriedKey::Key(keys[rng.below(keys.len())].clone()),
            });
        }
        out
    }

    /// A random defect-free fact graph. `closed` keeps every named principal
    /// recorded and adds no sink, so the pools close and rule H reads
    /// per-key summaries.
    fn random_graph(rng: &mut Rng, closed: bool) -> ReachGraph {
        let mut graph = ReachGraph::new();
        let count = 2 + rng.below(40);
        let mut nodes = Vec::new();
        let mut bodies = Vec::new();
        for id in 0..count {
            let body = match rng.below(12) {
                0 => NodeBody::Seed,
                1 if !closed => NodeBody::Opaque,
                2 => NodeBody::Param,
                3 => NodeBody::Primitive,
                _ => NodeBody::Walked,
            };
            let locality = if rng.chance(60) {
                Locality::Local
            } else {
                Locality::External
            };
            nodes.push(graph.add_node(ReachNodeSpec {
                origin: NodeOrigin::Mir(id as u32),
                definition: Some(DefinitionKey(rng.below(count / 2 + 1) as u128)),
                locality,
                body,
            }));
            bodies.push(body);
        }
        let sources: Vec<ReachNode> = (0..count)
            .filter(|index| bodies[*index] != NodeBody::Seed)
            .map(|index| nodes[index])
            .collect();
        if sources.is_empty() {
            return graph;
        }
        let keys = keys();
        // In a closed graph only the first principal is named, and every key
        // of it has a member.
        let usable: Vec<PoolKey> = if closed {
            keys.iter()
                .filter(|key| key.principal().is_none_or(|principal| principal.0 == 1))
                .cloned()
                .collect()
        } else {
            keys.clone()
        };
        let principals = if closed { 1 } else { 4 };
        let mut site = 0;
        let mut next_site = || {
            site += 1;
            ReachSite::Mir(site)
        };
        let classes = [
            EdgeClass::Run,
            EdgeClass::Create,
            EdgeClass::Read,
            EdgeClass::Param,
        ];
        for _ in 0..rng.below(count * 3) {
            let from = sources[rng.below(sources.len())];
            let to = nodes[rng.below(count)];
            let class = classes[rng.below(classes.len())];
            graph.add_edge(from, to, class, next_site(), rng.chance(20));
        }
        if !closed {
            for _ in 0..rng.below(3) {
                let from = sources[rng.below(sources.len())];
                graph.add_unknown(
                    from,
                    DependencyRefusalKind::UnresolvedExtern,
                    EdgeClass::Run,
                    next_site(),
                    false,
                );
            }
        }
        if closed {
            for key in &usable {
                if key.principal().is_some() {
                    let member = nodes[rng.below(count)];
                    graph.add_pool_member(member, key.clone(), false);
                }
            }
        }
        for _ in 0..rng.below(count * 2) {
            let creator = sources[rng.below(sources.len())];
            let member = nodes[rng.below(count)];
            let key = usable[rng.below(usable.len())].clone();
            if rng.chance(50) {
                graph.add_create(creator, member, key, rng.chance(30), next_site());
            } else {
                graph.add_pool_member(member, key, rng.chance(30));
            }
        }
        for _ in 0..rng.below(count * 2) {
            let node = sources[rng.below(sources.len())];
            let key = usable[rng.below(usable.len())].clone();
            let carried = if closed {
                let mut carried = carried(rng, &usable, principals);
                carried.retain(|key| {
                    !matches!(
                        key,
                        CarriedKey::AnyDyn | CarriedKey::Any | CarriedKey::Untyped
                    )
                });
                carried
            } else {
                carried(rng, &usable, principals)
            };
            graph.add_invoke(node, key, carried, next_site(), rng.chance(15));
        }
        for _ in 0..rng.below(count) {
            let node = sources[rng.below(sources.len())];
            let callee = nodes[rng.below(count)];
            let carried = carried(rng, &usable, principals);
            graph.add_handoff(node, callee, carried, next_site(), rng.chance(20));
        }
        if rng.chance(12) {
            graph.add_launder(next_site());
        }
        // Keyed LAUNDERs (design §10, "typed LAUNDER"): data holds what
        // their keys admit. Closed graphs draw keys of the recorded
        // principal only, so they stay closed.
        for _ in 0..rng.below(3) {
            if rng.chance(40) {
                let keys = carried(rng, &usable, principals);
                graph.add_launder_keys(next_site(), keys);
            }
        }
        if !closed && rng.chance(30) {
            graph.add_upcast(PrincipalKey(2), PrincipalKey(1));
        }
        if !closed && rng.chance(15) {
            graph.add_upcast(PrincipalKey(4), PrincipalKey(3));
        }
        if rng.chance(20) {
            graph.add_lifetime_erase(PrincipalKey(1));
        }
        graph
    }

    fn compare(graph: ReachGraph) -> (bool, usize) {
        let reference = Reference::solve(graph.clone());
        let census = graph.solve();
        let expanded = census.expanded();
        assert_eq!(census.fallback(), None);
        assert_eq!(
            check_reach_certificate(expanded, census.certificate()),
            Ok(())
        );
        // The same nodes in the same order, engine sinks included; hubs after.
        let count = reference.nodes.len();
        assert!(expanded.nodes.len() >= count);
        assert_eq!(expanded.nodes[..count], reference.nodes[..]);
        assert!(
            expanded.nodes[count..]
                .iter()
                .all(|kind| *kind == ReachNodeKind::Hub)
        );
        // The same logical edges, in the same order, with the same sites.
        assert_eq!(expanded.logical_edges(), reference.edges);
        // The same labels, definitions and witnesses.
        for index in 0..count {
            let node = expanded.handle(index);
            assert_eq!(
                census.verdict(node),
                reference.labels[index],
                "node {index}"
            );
            assert_eq!(
                census.witness(node),
                reference.witness(node),
                "node {index}"
            );
        }
        assert_eq!(
            census.certificate().definitions,
            reference.join_definitions(&reference.labels)
        );
        assert_eq!(census.spawn_sites(), Some(reference.spawn_sites()));
        for index in 0..count {
            let node = expanded.handle(index);
            let closure = census.thread_closure(Some(node));
            let (reached, modelable) = reference.thread_closure(node);
            assert_eq!(closure.reached, reached, "closure of {index}");
            assert_eq!(closure.modelable, modelable, "closure of {index}");
        }
        (
            expanded.pools().unclosed(),
            reference.edges.len() - reference.base_edges,
        )
    }

    /// Two local invokes of one pool whose external members include a
    /// thread start, from a node that RUNs it and from one that does not:
    /// rule H charges only the second with the hand-off into the seed. (The
    /// invoke's own edge to that member makes the hand-off's redundant, so
    /// no cached group list can change an edge here; this pins that the two
    /// derivations agree on the case, not the cache's seed exclusion.)
    #[test]
    fn a_seed_member_of_a_pool_splits_the_hand_off_by_its_caller() {
        let mut graph = ReachGraph::new();
        let spec = |id: u32, locality, body| ReachNodeSpec {
            origin: NodeOrigin::Mir(id),
            definition: Some(DefinitionKey(u128::from(id))),
            locality,
            body,
        };
        let seed = graph.add_node(spec(0, Locality::External, NodeBody::Seed));
        let runs = graph.add_node(spec(1, Locality::Local, NodeBody::Walked));
        let other = graph.add_node(spec(2, Locality::Local, NodeBody::Walked));
        let helper = graph.add_node(spec(3, Locality::External, NodeBody::Walked));
        let key = fn_key(Some(vec![]));
        graph.add_pool_member(seed, key.clone(), false);
        graph.add_pool_member(helper, key.clone(), false);
        graph.add_edge(runs, seed, EdgeClass::Run, ReachSite::Mir(1), false);
        for (node, site) in [(runs, 2), (other, 3)] {
            graph.add_invoke(
                node,
                key.clone(),
                vec![CarriedKey::AnyFn],
                ReachSite::Mir(site),
                false,
            );
        }
        compare(graph);
    }

    #[test]
    fn the_compressed_derivation_matches_the_uncompressed_one() {
        let mut rng = Rng(0xc0ff_ee15_b00c_a5e5);
        let (mut unclosed, mut closed, mut derived) = (0, 0, 0);
        for round in 0..3000 {
            let graph = random_graph(&mut rng, round % 3 == 0);
            let (open, edges) = compare(graph);
            if open {
                unclosed += 1;
            } else {
                closed += 1;
            }
            derived += edges;
        }
        // Not vacuous: both pool states occur, and pools derived edges.
        assert!(unclosed > 500 && closed > 500, "{unclosed} / {closed}");
        assert!(derived > 10_000, "{derived}");
    }
}

/// The rule H carrier walk of a census pass: one all-definitions index for
/// the pass, and one walk per signature however many call sites share it.
#[cfg(test)]
mod signature_carries_tests {
    use super::*;
    use crate::ty::{FieldDef, FuncTy, StructDef, StructRepr};
    use crate::value::{BlockId, StructId, ValueId};
    use crate::{Block, CallingConv, Function, Inst, InstrNode};

    struct Classes;

    impl DeclClassifier for Classes {
        fn classify(&self, function: &Function) -> FunctionClass {
            if function.is_declaration() {
                FunctionClass::Foreign
            } else {
                FunctionClass::Walk
            }
        }

        fn definition(&self, function: &Function) -> DefinitionKey {
            DefinitionKey(u128::from(function.id.index()))
        }

        fn runtime_service(&self, _: RuntimeService) -> ServiceClass {
            ServiceClass::Foreign
        }
    }

    fn strukt(id: u32, ty: Ty) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: vec![FieldDef {
                name: "f".into(),
                ty,
                offset: None,
            }],
            size: None,
            align: None,
            repr: StructRepr::C,
            origin: None,
        }
    }

    /// Function 0 makes `sites` indirect calls through an unknown callee and
    /// `sites` calls of the foreign declaration 1, all over the signature
    /// `(S{depth-1}) -> ()`, where `S0 = { fn() }` and `S{k} = { S{k-1} }`.
    fn module(depth: u32, sites: usize) -> Module {
        let mut module = Module::new("signature_carries");
        let unit = FuncTyId::new(0);
        module.func_types.push(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        let carrying = FuncTyId::new(1);
        module.func_types.push(FuncTy {
            params: vec![Ty::Struct(StructId::new(depth - 1))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        module.structs.push(strukt(0, Ty::Func(unit)));
        for k in 1..depth {
            module
                .structs
                .push(strukt(k, Ty::Struct(StructId::new(k - 1))));
        }
        let mut body = Vec::new();
        for _ in 0..sites {
            body.push(InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: carrying,
                args: vec![],
                calling_conv: CallingConv::C,
            }));
            body.push(InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![],
            }));
        }
        body.push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut caller = Function::new(FuncId::new(0), "caller", unit, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body = body;
        caller.blocks.push(block);
        module.functions.push(caller);
        module.functions.push(Function::new(
            FuncId::new(1),
            "foreign",
            carrying,
            BlockId::new(0),
        ));
        module
    }

    #[test]
    fn every_call_site_of_a_signature_shares_one_walk_and_one_index() {
        for (depth, sites) in [(1, 1), (8, 3), (200, 2000)] {
            let module = module(depth, sites);
            let walker = ReachWalker::walk(&module, &Classes);
            let carries = &walker.carries;
            // One signature, walked once, for 2 * `sites` call sites ...
            assert_eq!(carries.walks, 1, "{depth} {sites}");
            assert_eq!(carries.keys.len(), 1, "{depth} {sites}");
            // ... over one index of the struct table, read once.
            assert_eq!(carries.defs.rows_indexed, module.structs.len());
            // The keys are the walk's: S{depth-1} carries `fn()` by value.
            let keys = &carries.keys[&FuncTyId::new(1)];
            let fresh = carried_keys(
                &module,
                &mut crate::reach::DefIndex::default(),
                &module.func_types[1].params[0],
            );
            assert_eq!(keys, &fresh);
            assert!(
                keys.iter()
                    .any(|key| matches!(key, CarriedKey::Key(PoolKey::Fn(_)))),
                "{keys:?}"
            );
        }
    }
}
