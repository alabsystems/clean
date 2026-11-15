// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Frontend-neutral, fail-closed analyses over core TrustIr.
//!
//! These analyses live with the IR instead of in an individual validator or
//! backend so every consumer makes the same conservative decision.  They do
//! not mutate a module and do not confer proof authority.

use std::collections::{BTreeMap, BTreeSet, btree_map::Entry};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::OnceLock;

use crate::constant::Constant;
use crate::function_dependencies::{ReachNode, ReachSite};
use crate::inst::{CastOp, Inst};
use crate::ty::{FatPtrKind, StructRepr, Ty};
use crate::value::{BlockId, FuncId, FuncTyId, ValueId};
use crate::{Block, Function, Module, NominalTypeReachability};

mod observed_dominators;
mod observed_function_pointers;
pub use observed_function_pointers::ObservedStaticFunctionPointerAnalysis;
#[allow(
    dead_code,
    reason = "the observed pool closure is staged by the observed-r23 lane with no production caller yet; its tests drive it"
)]
mod observed_pools;
mod pointer_roots;
pub use pointer_roots::{PointerRoot, PointerRoots, pointer_roots};

// Keep the rejection-only per-use prefilter constant-time in the size of the
// use block.  A nine-instruction window around the use catches the common
// lowering shape without turning many indirect calls in one block into a
// quadratic scan.  Anything outside the window is decided by the shared lazy
// index.
const LOCAL_PREFILTER_INSTRUCTION_LIMIT: usize = 9;

/// Physical carrier proven for a statically resolved function pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StaticFunctionPointerCarrier {
    /// A typed function identity.
    Function(FuncTyId),
    /// A materialized raw code pointer.
    Pointer,
}

/// Typed, dominance-safe resolution of one static function pointer.
///
/// `declared_signature` is the signature on the originating `Const(FnDef)`.
/// A module-level consumer must still prove that it is the exact signature of
/// `function`; this function-local analysis deliberately does not choose among
/// module declarations.  This is an ephemeral analysis result, not a proof or
/// transformation-authority token: a module consumer must use it immediately
/// against the same containing function, reject missing or ambiguous targets,
/// and mint any durable validation receipt at that stronger boundary.  The
/// fields are private so downstream code cannot manufacture even this local
/// result; accessors expose the exact queried value/use coordinates and
/// originating definition bound by the analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StaticFunctionPointerResolution {
    /// Function body in which the exact use was authenticated.
    containing_function: FuncId,
    /// Exact module-local function identity carried by the value.
    function: FuncId,
    /// Function signature declared at the originating `Const(FnDef)`.
    declared_signature: FuncTyId,
    /// Type-safe carrier at the requested use site.
    carrier: StaticFunctionPointerCarrier,
    queried_value: ValueId,
    use_block: BlockId,
    use_instruction_index: usize,
    origin_value: ValueId,
    origin_block: BlockId,
    origin_instruction_index: usize,
    chain_definitions: usize,
}

impl StaticFunctionPointerResolution {
    /// Function body in which the exact use was authenticated.
    #[must_use]
    pub fn containing_function(&self) -> FuncId {
        self.containing_function
    }

    /// Exact module-local function identity carried by the value.
    #[must_use]
    pub fn function(&self) -> FuncId {
        self.function
    }

    /// Signature declared by the originating `Const(FnDef)`.
    #[must_use]
    pub fn declared_signature(&self) -> FuncTyId {
        self.declared_signature
    }

    /// Type-safe physical carrier at the exact queried use.
    #[must_use]
    pub fn carrier(&self) -> StaticFunctionPointerCarrier {
        self.carrier
    }

    /// SSA value whose exact use was authenticated.
    #[must_use]
    pub fn queried_value(&self) -> ValueId {
        self.queried_value
    }

    /// Block containing the authenticated consuming instruction.
    #[must_use]
    pub fn use_block(&self) -> BlockId {
        self.use_block
    }

    /// Index of the authenticated consuming instruction within [`Self::use_block`].
    #[must_use]
    pub fn use_instruction_index(&self) -> usize {
        self.use_instruction_index
    }

    /// SSA result produced by the originating `Const(FnDef)`.
    #[must_use]
    pub fn origin_value(&self) -> ValueId {
        self.origin_value
    }

    /// Block containing the originating `Const(FnDef)`.
    #[must_use]
    pub fn origin_block(&self) -> BlockId {
        self.origin_block
    }

    /// Instruction index of the originating `Const(FnDef)`.
    #[must_use]
    pub fn origin_instruction_index(&self) -> usize {
        self.origin_instruction_index
    }

    /// Number of definitions in the authenticated FnDef/Copy/Reify chain.
    #[must_use]
    pub fn chain_definitions(&self) -> usize {
        self.chain_definitions
    }
}

#[derive(Debug, Clone, Copy)]
enum DefinitionState<'function> {
    Unique {
        instruction: Option<&'function Inst>,
        block: BlockId,
        instruction_index: Option<usize>,
    },
    Ambiguous,
}

#[derive(Debug)]
struct DefinitionIndex<'function> {
    entries: BTreeMap<u32, DefinitionState<'function>>,
}

#[derive(Debug)]
enum UseBlockState<'function> {
    Unique {
        block: &'function Block,
        parameters: BTreeSet<u32>,
    },
    Ambiguous,
}

#[derive(Debug)]
struct UseSiteIndex<'function> {
    blocks: BTreeMap<u32, UseBlockState<'function>>,
}

#[derive(Debug, Clone, Copy)]
struct StaticProvenanceSummary<'function> {
    function: FuncId,
    declared_signature: FuncTyId,
    carrier: StaticFunctionPointerCarrier,
    result_type: &'function Ty,
    definition_block: BlockId,
    definition_instruction: usize,
    origin_value: ValueId,
    origin_block: BlockId,
    origin_instruction: usize,
    chain_definitions: usize,
}

#[derive(Debug, Clone, Copy)]
enum ProvenanceState<'function> {
    Resolved(StaticProvenanceSummary<'function>),
    Rejected,
}

#[derive(Debug)]
struct ProvenanceIndex<'function> {
    entries: BTreeMap<u32, ProvenanceState<'function>>,
}

#[derive(Debug, Clone, Copy)]
enum ProvenanceStep<'function> {
    Copy {
        result_type: &'function Ty,
        operand: ValueId,
        definition_block: BlockId,
        definition_instruction: usize,
    },
    Reify {
        source_type: &'function Ty,
        result_type: &'function Ty,
        operand: ValueId,
        definition_block: BlockId,
        definition_instruction: usize,
    },
}

/// Which lazy whole-function components have been initialized.
///
/// Reading this snapshot does not initialize an analysis component or update a
/// counter.  A consumer can compare snapshots around one query to account for
/// actual lazy work without instrumenting the normal resolver path.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct StaticFunctionPointerCacheState {
    /// The exact block/parameter use-site index has been built.
    pub use_site_index_built: bool,
    /// The whole-function SSA definition index has been built.
    pub definition_index_built: bool,
    /// The memoized, dominance-checked provenance summaries have been built.
    pub provenance_index_built: bool,
    /// The CFG dominator tree has been built.
    pub dominator_tree_built: bool,
}

/// Selected structural work performed by one opt-in typed-resolution query.
///
/// Normal [`StaticFunctionPointerAnalysis::resolve_typed_at`] queries do not
/// maintain counters.  This value is populated only by
/// [`StaticFunctionPointerAnalysis::resolve_typed_at_with_census`], allowing a
/// tracing consumer to measure the explicitly named visits without imposing
/// atomic or counter writes on untraced compilation.  It is not a CPU-cycle or
/// allocator census; ordered-map probes, dominator-fixpoint rounds and
/// intersections, and scalar bookkeeping are omitted.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct StaticFunctionPointerQueryCensus {
    /// Block declarations scanned if this query initialized the use-site index.
    pub use_site_blocks_indexed: usize,
    /// Block parameters scanned if this query initialized the use-site index.
    pub use_site_parameters_indexed: usize,
    /// Instructions examined by the constant-bounded local prefilter.
    pub prefilter_instructions_visited: usize,
    /// SSA operands examined while authenticating the exact consuming node.
    pub exact_use_operands_visited: usize,
    /// Blocks scanned if this query initialized the definition index.
    pub definition_blocks_indexed: usize,
    /// Instructions scanned if this query initialized the definition index.
    pub definition_instructions_indexed: usize,
    /// SSA value declarations recorded if this query initialized that index.
    pub definition_values_indexed: usize,
    /// Definition entries examined while seeding and walking provenance.
    pub provenance_definitions_visited: usize,
    /// Candidate Copy/Reify links traversed while initializing provenance,
    /// including links whose chain is later rejected or found cyclic.
    pub provenance_links_validated: usize,
    /// Candidate-chain summaries retained in the sparse provenance index.
    pub provenance_entries_stored: usize,
    /// Block declarations indexed by the CFG uniqueness pass if initialized.
    pub dominator_blocks_indexed: usize,
    /// Instructions scanned if this query initialized CFG dominance.
    pub dominator_instructions_indexed: usize,
    /// CFG successor edges recorded if this query initialized dominance.
    pub dominator_edges_indexed: usize,
    /// Memoized provenance summaries looked up by this query.
    pub provenance_summary_lookups: usize,
    /// Top-definition to exact-use dominance checks performed by this query.
    pub exact_use_dominance_checks: usize,
}

/// Same-function analysis for statically visible function-pointer provenance.
///
/// The recognized subset is deliberately small and checkable: a value must be
/// defined by `Const(FnDef)` or by a chain of [`Inst::Copy`] and
/// [`CastOp::ReifyFnPointer`] operations leading to one.  Values arriving via
/// block parameters, memory, selects, raw-pointer casts, closure environments,
/// or another function remain dynamic.
///
/// Construction retains only the function reference.  Exact use-site,
/// definition, sparse provenance-summary, and dominance indexes are initialized
/// independently on the first query that needs each of them, so obviously
/// dynamic use-site operands require no definition or CFG work.  A resolver can
/// then be reused for every indirect call in that function.  For `D` indexed
/// definitions and `Q` typed queries, shared-chain provenance work performs
/// `O(D + Q)` producer visits overall; ordered-map probes add logarithmic
/// factors.  That bound is deliberately not a total-time claim. If exact-use
/// authentication examines `U` operands it adds `O(U)` work. For `I`
/// instructions, `B` reachable blocks, `E` CFG edges, and `R` dominator
/// fixpoint rounds, the one-time CFG analysis has the conservative ordered-map
/// bound `O((I + B + E) log B + R * (B + E * B) log B)`; the `E * B` term
/// accounts for worst-case ancestor climbing during predecessor intersections.
/// Exact dominance queries add `O(Q log B)`. Block parameters, multi-result
/// definitions, duplicate SSA definitions, and cyclic chains fail closed.
/// There is no arbitrary chain-length ceiling.
#[derive(Debug)]
pub struct StaticFunctionPointerAnalysis<'function> {
    function: &'function Function,
    use_sites: OnceLock<UseSiteIndex<'function>>,
    definitions: OnceLock<DefinitionIndex<'function>>,
    provenances: OnceLock<ProvenanceIndex<'function>>,
    dominators: OnceLock<DominatorTree>,
}

impl<'function> StaticFunctionPointerAnalysis<'function> {
    /// Create a lazy analysis without scanning or allocating for `function`.
    #[must_use]
    pub fn new(function: &'function Function) -> Self {
        Self {
            function,
            use_sites: OnceLock::new(),
            definitions: OnceLock::new(),
            provenances: OnceLock::new(),
            dominators: OnceLock::new(),
        }
    }

    fn definitions(&self) -> &DefinitionIndex<'function> {
        self.definitions
            .get_or_init(|| build_definition_index(self.function, None))
    }

    /// Return a zero-write snapshot of the lazy component state.
    #[must_use]
    pub fn cache_state(&self) -> StaticFunctionPointerCacheState {
        StaticFunctionPointerCacheState {
            use_site_index_built: self.use_sites.get().is_some(),
            definition_index_built: self.definitions.get().is_some(),
            provenance_index_built: self.provenances.get().is_some(),
            dominator_tree_built: self.dominators.get().is_some(),
        }
    }

    /// Return the reusable CFG dominance context, initializing it once.
    ///
    /// Validators that already require dominance for SSA checking can use this
    /// context and then share the exact same facts with typed static-pointer
    /// resolution instead of constructing a second CFG analysis.
    #[must_use]
    pub fn dominator_tree(&self) -> &DominatorTree {
        self.dominators
            .get_or_init(|| DominatorTree::new(self.function))
    }

    fn dominator_tree_with_census(
        &self,
        census: Option<&mut StaticFunctionPointerQueryCensus>,
    ) -> &DominatorTree {
        self.dominators
            .get_or_init(|| compute_dominator_tree(self.function, census))
    }

    /// Resolve `value` to an exact module-local [`FuncId`] when its provenance
    /// is entirely within the checkable subset described on this type.
    ///
    /// This compatibility API deliberately does not authenticate a type, CFG,
    /// or use site and must not authorize a transformation.  It may walk the
    /// chain on each call.  Consumers handling indirect-call sites should reuse
    /// [`Self::resolve_typed_at`], whose sparse summaries amortize shared chains
    /// across exact queries.
    #[must_use]
    pub fn resolve(&self, value: ValueId) -> Option<FuncId> {
        let definitions = &self.definitions().entries;
        let mut current = value;
        // Acyclic single-definition provenance can traverse at most one entry
        // per indexed definition.  One additional step therefore detects any
        // malformed cycle without a per-query visited-set allocation.
        for _ in 0..=definitions.len() {
            match definitions.get(&current.index())? {
                DefinitionState::Unique {
                    instruction:
                        Some(Inst::Const {
                            value: Constant::FnDef(function),
                            ..
                        }),
                    ..
                } => return Some(*function),
                DefinitionState::Unique {
                    instruction: Some(Inst::Copy { operand, .. }),
                    ..
                } => current = *operand,
                DefinitionState::Unique {
                    instruction:
                        Some(Inst::Cast {
                            op: CastOp::ReifyFnPointer,
                            operand,
                            ..
                        }),
                    ..
                } => current = *operand,
                // Block parameters, ambiguous definitions, and every other
                // instruction are outside this intentionally exact subset.
                DefinitionState::Unique {
                    instruction: None, ..
                }
                | DefinitionState::Unique {
                    instruction: Some(_),
                    ..
                }
                | DefinitionState::Ambiguous => return None,
            }
        }

        None
    }

    /// Resolve one function pointer at an exact instruction use site.
    ///
    /// Unlike [`Self::resolve`], this API authenticates an exact use for a
    /// module consumer to validate immediately.  It proves that every
    /// definition in the `FnDef` / `Copy` /
    /// `ReifyFnPointer` chain dominates its immediate consumer, that the use is
    /// reachable in a structurally usable CFG, and that every carrier
    /// transition is type exact.  Same-block forward references, sibling-block
    /// definitions, malformed CFGs, duplicate ids, unsupported casts, and type
    /// laundering all return `None`.  The returned function-local result is not
    /// durable proof authority; see [`StaticFunctionPointerResolution`].
    #[must_use]
    pub fn resolve_typed_at(
        &self,
        value: ValueId,
        use_block: BlockId,
        use_instruction_index: usize,
    ) -> Option<StaticFunctionPointerResolution> {
        self.resolve_typed_at_impl(value, use_block, use_instruction_index, None)
    }

    /// Resolve one function pointer and report selected structural work.
    ///
    /// This is the opt-in instrumentation counterpart of
    /// [`Self::resolve_typed_at`].  The ordinary API has no counter writes;
    /// callers that collect statistics can use this method and compare
    /// [`Self::cache_state`] snapshots around it.
    #[must_use]
    pub fn resolve_typed_at_with_census(
        &self,
        value: ValueId,
        use_block: BlockId,
        use_instruction_index: usize,
    ) -> (
        Option<StaticFunctionPointerResolution>,
        StaticFunctionPointerQueryCensus,
    ) {
        let mut census = StaticFunctionPointerQueryCensus::default();
        let resolution =
            self.resolve_typed_at_impl(value, use_block, use_instruction_index, Some(&mut census));
        (resolution, census)
    }

    fn resolve_typed_at_impl(
        &self,
        value: ValueId,
        use_block: BlockId,
        use_instruction_index: usize,
        mut census: Option<&mut StaticFunctionPointerQueryCensus>,
    ) -> Option<StaticFunctionPointerResolution> {
        // Locate and authenticate the exact use site through one reusable lazy
        // index.  This removes a blocks-times-calls scan while preserving
        // fail-closed handling of duplicate block IDs.
        let use_sites = self
            .use_sites
            .get_or_init(|| build_use_site_index(self.function, census.as_deref_mut()));
        let UseBlockState::Unique {
            block: use_block_ref,
            parameters,
        } = use_sites.blocks.get(&use_block.index())?
        else {
            return None;
        };
        let use_node = use_block_ref.body.get(use_instruction_index)?;

        // Coordinates alone are not evidence that this instruction consumes
        // the queried value.  Reject before provenance/dominance initialization
        // so an unrelated later instruction cannot authenticate a forward
        // definition.
        let exact_use_found = use_node
            .inst
            .try_visit_value_operands(|operand| {
                if let Some(census) = census.as_deref_mut() {
                    census.exact_use_operands_visited += 1;
                }
                if operand == value {
                    std::ops::ControlFlow::Break(())
                } else {
                    std::ops::ControlFlow::Continue(())
                }
            })
            .is_break();
        if !exact_use_found {
            return None;
        }

        // A block parameter is dynamic at this same-function analysis boundary.
        // Parameter membership is indexed once, so repeated dynamic calls do
        // not rescan a large parameter list.
        if parameters.contains(&value.index()) {
            return None;
        }

        // This is a rejection-only local prefilter.  A locally visible
        // definition cannot be accepted when it is an unsupported producer,
        // malformed/duplicate, or does not precede the use.  Absence of any of
        // these conditions proves nothing; authoritative duplicate, type,
        // dominance, and CFG checks still run below for every accepted value.
        if self.provenances.get().is_none() {
            let prefilter_visits = census
                .as_deref_mut()
                .map(|census| &mut census.prefilter_instructions_visited);
            if locally_obvious_dynamic_value(
                use_block_ref,
                value,
                use_instruction_index,
                prefilter_visits,
            ) {
                return None;
            }
        }

        let definition_index = self
            .definitions
            .get_or_init(|| build_definition_index(self.function, census.as_deref_mut()));
        let definitions = &definition_index.entries;

        // Refuse an unsupported top-level producer before paying for CFG or
        // provenance-summary construction.  The full index remains the
        // authority for duplicates, cycles, types, and every internal edge.
        let DefinitionState::Unique {
            instruction: Some(top_instruction),
            ..
        } = definitions.get(&value.index())?
        else {
            return None;
        };
        match static_pointer_definition_type(top_instruction)? {
            Ty::Func(_) | Ty::Ptr => {}
            _ => return None,
        }

        let dominators = self.dominator_tree_with_census(census.as_deref_mut());
        if !dominators.is_well_formed() || !dominators.is_reachable(use_block) {
            return None;
        }

        // Summarize every functional producer chain once.  Internal
        // Copy/Reify dominance and type transitions are cached; each use still
        // proves its own top-definition dominance below.
        let provenances = self.provenances.get_or_init(|| {
            build_provenance_index(definition_index, dominators, census.as_deref_mut())
        });
        if let Some(census) = &mut census {
            census.provenance_summary_lookups += 1;
        }
        let ProvenanceState::Resolved(summary) = provenances.entries.get(&value.index())? else {
            return None;
        };

        if let Some(census) = &mut census {
            census.exact_use_dominance_checks += 1;
        }
        if !definition_dominates_use(
            dominators,
            summary.definition_block,
            summary.definition_instruction,
            use_block,
            use_instruction_index,
        ) {
            return None;
        }

        Some(StaticFunctionPointerResolution {
            containing_function: self.function.id,
            function: summary.function,
            declared_signature: summary.declared_signature,
            carrier: summary.carrier,
            queried_value: value,
            use_block,
            use_instruction_index,
            origin_value: summary.origin_value,
            origin_block: summary.origin_block,
            origin_instruction_index: summary.origin_instruction,
            chain_definitions: summary.chain_definitions,
        })
    }
}

fn build_definition_index<'function>(
    function: &'function Function,
    mut census: Option<&mut StaticFunctionPointerQueryCensus>,
) -> DefinitionIndex<'function> {
    let mut definitions = BTreeMap::new();
    for block in &function.blocks {
        if let Some(census) = census.as_deref_mut() {
            census.definition_blocks_indexed += 1;
        }
        // A block parameter is a real SSA definition, but its incoming value
        // is dynamic at this local analysis boundary.
        for (parameter, _) in &block.params {
            if let Some(census) = census.as_deref_mut() {
                census.definition_values_indexed += 1;
            }
            record_definition(
                &mut definitions,
                *parameter,
                DefinitionState::Unique {
                    instruction: None,
                    block: block.id,
                    instruction_index: None,
                },
            );
        }
        for (instruction_index, node) in block.body.iter().enumerate() {
            if let Some(census) = census.as_deref_mut() {
                census.definition_instructions_indexed += 1;
                census.definition_values_indexed += node.results.len();
            }
            if node.results.len() == 1 {
                record_definition(
                    &mut definitions,
                    node.results[0],
                    DefinitionState::Unique {
                        instruction: Some(&node.inst),
                        block: block.id,
                        instruction_index: Some(instruction_index),
                    },
                );
            } else {
                // Static pointer-producing instructions are single-result.
                // Index every malformed extra result as non-resolvable so it
                // cannot alias a separately declared definition.
                for result in &node.results {
                    record_definition(&mut definitions, *result, DefinitionState::Ambiguous);
                }
            }
        }
    }
    DefinitionIndex {
        entries: definitions,
    }
}

fn build_use_site_index<'function>(
    function: &'function Function,
    mut census: Option<&mut StaticFunctionPointerQueryCensus>,
) -> UseSiteIndex<'function> {
    let mut blocks = BTreeMap::new();
    for block in &function.blocks {
        if let Some(census) = census.as_deref_mut() {
            census.use_site_blocks_indexed += 1;
            census.use_site_parameters_indexed += block.params.len();
        }
        let state = UseBlockState::Unique {
            block,
            parameters: block
                .params
                .iter()
                .map(|(parameter, _)| parameter.index())
                .collect(),
        };
        match blocks.entry(block.id.index()) {
            Entry::Vacant(entry) => {
                entry.insert(state);
            }
            Entry::Occupied(mut entry) => {
                entry.insert(UseBlockState::Ambiguous);
            }
        }
    }
    UseSiteIndex { blocks }
}

fn build_provenance_index<'function>(
    definitions: &DefinitionIndex<'function>,
    dominators: &DominatorTree,
    mut census: Option<&mut StaticFunctionPointerQueryCensus>,
) -> ProvenanceIndex<'function> {
    let mut entries = BTreeMap::new();
    let mut active = BTreeSet::new();

    // Every candidate producer has at most one predecessor, so iterative path
    // compression summarizes the entire graph without recursion.  A value is
    // placed on one path at most once; cycles and every prefix reaching one are
    // cached as rejected.
    for (&start, definition) in &definitions.entries {
        if let Some(census) = census.as_deref_mut() {
            census.provenance_definitions_visited += 1;
        }
        if !is_static_provenance_candidate(definition) {
            continue;
        }
        if entries.contains_key(&start) {
            continue;
        }

        let mut path = Vec::<(u32, ProvenanceStep<'function>)>::new();
        let mut current = start;
        let mut reached_cycle = false;
        loop {
            if entries.contains_key(&current) {
                break;
            }
            if active.contains(&current) {
                reached_cycle = true;
                break;
            }

            let Some(definition) = definitions.entries.get(&current) else {
                break;
            };
            if let Some(census) = census.as_deref_mut() {
                census.provenance_definitions_visited += 1;
            }
            // Candidate eligibility is a closure invariant, not merely a
            // seed filter.  A malformed pointer-typed Copy can point into an
            // arbitrarily large ordinary data-copy graph; stopping here keeps
            // the memo sparse instead of retaining one Rejected row per
            // non-function value reached from that malformed edge.
            if !is_static_provenance_candidate(definition) {
                break;
            }

            match *definition {
                DefinitionState::Unique {
                    instruction:
                        Some(Inst::Const {
                            ty: result_type @ Ty::Func(declared_signature),
                            value: Constant::FnDef(function),
                        }),
                    block: definition_block,
                    instruction_index: Some(definition_instruction),
                } => {
                    entries.insert(
                        current,
                        ProvenanceState::Resolved(StaticProvenanceSummary {
                            function: *function,
                            declared_signature: *declared_signature,
                            carrier: StaticFunctionPointerCarrier::Function(*declared_signature),
                            result_type,
                            definition_block,
                            definition_instruction,
                            origin_value: ValueId::new(current),
                            origin_block: definition_block,
                            origin_instruction: definition_instruction,
                            chain_definitions: 1,
                        }),
                    );
                    break;
                }
                DefinitionState::Unique {
                    instruction: Some(Inst::Copy { ty, operand }),
                    block: definition_block,
                    instruction_index: Some(definition_instruction),
                } => {
                    if let Some(census) = census.as_deref_mut() {
                        census.provenance_links_validated += 1;
                    }
                    active.insert(current);
                    path.push((
                        current,
                        ProvenanceStep::Copy {
                            result_type: ty,
                            operand: *operand,
                            definition_block,
                            definition_instruction,
                        },
                    ));
                    current = operand.index();
                }
                DefinitionState::Unique {
                    instruction:
                        Some(Inst::Cast {
                            op: CastOp::ReifyFnPointer,
                            src_ty,
                            dst_ty,
                            operand,
                        }),
                    block: definition_block,
                    instruction_index: Some(definition_instruction),
                } => {
                    if let Some(census) = census.as_deref_mut() {
                        census.provenance_links_validated += 1;
                    }
                    active.insert(current);
                    path.push((
                        current,
                        ProvenanceStep::Reify {
                            source_type: src_ty,
                            result_type: dst_ty,
                            operand: *operand,
                            definition_block,
                            definition_instruction,
                        },
                    ));
                    current = operand.index();
                }
                DefinitionState::Unique { .. } | DefinitionState::Ambiguous => break,
            }
        }

        if reached_cycle {
            for (value, _) in path.drain(..) {
                active.remove(&value);
                entries.insert(value, ProvenanceState::Rejected);
            }
            continue;
        }

        while let Some((value, step)) = path.pop() {
            active.remove(&value);
            let operand = match step {
                ProvenanceStep::Copy { operand, .. } | ProvenanceStep::Reify { operand, .. } => {
                    operand
                }
            };
            let child = entries
                .get(&operand.index())
                .copied()
                .unwrap_or(ProvenanceState::Rejected);
            entries.insert(value, extend_static_provenance(child, step, dominators));
        }
    }

    if let Some(census) = census {
        census.provenance_entries_stored = entries.len();
    }
    ProvenanceIndex { entries }
}

fn is_static_provenance_candidate(definition: &DefinitionState<'_>) -> bool {
    matches!(
        definition,
        DefinitionState::Unique {
            instruction: Some(
                Inst::Const {
                    ty: Ty::Func(_),
                    value: Constant::FnDef(_),
                } | Inst::Copy {
                    ty: Ty::Func(_) | Ty::Ptr,
                    ..
                } | Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: Ty::Func(_),
                    dst_ty: Ty::Ptr,
                    ..
                } | Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::Func(_),
                    ..
                }
            ),
            instruction_index: Some(_),
            ..
        }
    )
}

fn extend_static_provenance<'function>(
    child: ProvenanceState<'function>,
    step: ProvenanceStep<'function>,
    dominators: &DominatorTree,
) -> ProvenanceState<'function> {
    let ProvenanceState::Resolved(child) = child else {
        return ProvenanceState::Rejected;
    };

    let (result_type, definition_block, definition_instruction, transition_is_exact) = match step {
        ProvenanceStep::Copy {
            result_type,
            definition_block,
            definition_instruction,
            ..
        } => (
            result_type,
            definition_block,
            definition_instruction,
            child.result_type == result_type
                && carrier_for_signature(result_type, child.declared_signature).is_some(),
        ),
        ProvenanceStep::Reify {
            source_type,
            result_type,
            definition_block,
            definition_instruction,
            ..
        } => (
            result_type,
            definition_block,
            definition_instruction,
            child.result_type == source_type
                && matches!(
                    (source_type, result_type),
                    (Ty::Func(_), Ty::Ptr) | (Ty::Ptr, Ty::Func(_))
                )
                && carrier_for_signature(source_type, child.declared_signature).is_some()
                && carrier_for_signature(result_type, child.declared_signature).is_some(),
        ),
    };

    if !transition_is_exact
        || !dominators.is_reachable(definition_block)
        || !definition_dominates_use(
            dominators,
            child.definition_block,
            child.definition_instruction,
            definition_block,
            definition_instruction,
        )
    {
        return ProvenanceState::Rejected;
    }

    let Some(carrier) = carrier_for_signature(result_type, child.declared_signature) else {
        return ProvenanceState::Rejected;
    };
    let Some(chain_definitions) = child.chain_definitions.checked_add(1) else {
        return ProvenanceState::Rejected;
    };
    ProvenanceState::Resolved(StaticProvenanceSummary {
        carrier,
        result_type,
        definition_block,
        definition_instruction,
        chain_definitions,
        ..child
    })
}

fn carrier_for_signature(
    ty: &Ty,
    declared_signature: FuncTyId,
) -> Option<StaticFunctionPointerCarrier> {
    match ty {
        Ty::Func(signature) if *signature == declared_signature => {
            Some(StaticFunctionPointerCarrier::Function(*signature))
        }
        Ty::Ptr => Some(StaticFunctionPointerCarrier::Pointer),
        _ => None,
    }
}

/// Cheap rejection using only the already-located use block.
///
/// Returning `false` is not evidence of static provenance.  Returning `true`
/// is sound because every case is either dynamic by definition or would be
/// rejected by the authoritative duplicate/dominance checks.  The instruction
/// scan is deliberately bounded so repeated calls in one large block remain
/// linear overall; values outside the window fall through to the lazy index.
fn locally_obvious_dynamic_value(
    use_block: &Block,
    value: ValueId,
    use_instruction_index: usize,
    mut instruction_visits: Option<&mut usize>,
) -> bool {
    let mut local_definition = None;
    let instruction_window =
        local_prefilter_instruction_window(use_block.body.len(), use_instruction_index);
    for (instruction_offset, node) in use_block.body[instruction_window.clone()]
        .iter()
        .enumerate()
    {
        if let Some(instruction_visits) = instruction_visits.as_deref_mut() {
            *instruction_visits += 1;
        }
        let instruction_index = instruction_window.start + instruction_offset;
        // Inspect at most one result per instruction.  A malformed
        // multi-result node is left to the shared definition index; scanning
        // an attacker-sized result vector here would defeat the constant
        // prefilter bound across many calls.
        let [result] = node.results.as_slice() else {
            continue;
        };
        if *result != value {
            continue;
        }

        if !matches!(
            &node.inst,
            Inst::Const {
                value: Constant::FnDef(_),
                ..
            } | Inst::Copy { .. }
                | Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    ..
                }
        ) || local_definition.replace(instruction_index).is_some()
        {
            return true;
        }
    }

    local_definition.is_some_and(|definition_index| definition_index >= use_instruction_index)
}

fn local_prefilter_instruction_window(
    block_len: usize,
    use_instruction_index: usize,
) -> std::ops::Range<usize> {
    let instructions_before_use = LOCAL_PREFILTER_INSTRUCTION_LIMIT / 2;
    let start = use_instruction_index.saturating_sub(instructions_before_use);
    let end = start
        .saturating_add(LOCAL_PREFILTER_INSTRUCTION_LIMIT)
        .min(block_len);
    start..end
}

fn record_definition<'function>(
    definitions: &mut BTreeMap<u32, DefinitionState<'function>>,
    value: ValueId,
    definition: DefinitionState<'function>,
) {
    match definitions.entry(value.index()) {
        Entry::Vacant(entry) => {
            entry.insert(definition);
        }
        Entry::Occupied(mut entry) => {
            // Malformed SSA must not let a consumer pick whichever definition
            // happened to win declaration order.
            entry.insert(DefinitionState::Ambiguous);
        }
    }
}

fn static_pointer_definition_type(instruction: &Inst) -> Option<&Ty> {
    match instruction {
        Inst::Const {
            value: Constant::FnDef(_),
            ty,
        }
        | Inst::Copy { ty, .. } => Some(ty),
        Inst::Cast {
            op: CastOp::ReifyFnPointer,
            dst_ty,
            ..
        } => Some(dst_ty),
        _ => None,
    }
}

fn definition_dominates_use(
    dominators: &DominatorTree,
    definition_block: BlockId,
    definition_instruction: usize,
    use_block: BlockId,
    use_instruction: usize,
) -> bool {
    if definition_block == use_block {
        definition_instruction < use_instruction
    } else {
        dominators.strictly_dominates(definition_block, use_block)
    }
}

/// Dominance over structurally usable blocks reachable from a function entry.
///
/// Construction uses the Cooper/Harvey/Kennedy immediate-dominator algorithm
/// and retains `O(blocks + edges)` graph state.  Queries are constant-time
/// apart from ordered-map lookup.  Duplicate block ids, an absent entry,
/// unknown branch targets, misplaced terminators, or unterminated blocks make
/// the analysis invalid; every query then fails closed.
#[derive(Debug, Default)]
pub struct DominatorTree {
    well_formed: bool,
    reachable: BTreeSet<u32>,
    immediate_dominator: BTreeMap<u32, u32>,
    preorder: BTreeMap<u32, usize>,
    postorder: BTreeMap<u32, usize>,
    instruction_counts: BTreeMap<u32, usize>,
    invoke_instructions: BTreeMap<u32, usize>,
    dominating_edges: BTreeMap<(u32, usize), u32>,
}

/// Actual SSA definition coordinates, supplied by a consumer's definition index.
/// `None` denotes a block parameter; instruction positions are zero-based.
/// Coordinates are not proof authority or a substitute for unique SSA binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SsaDefinitionSite {
    pub block: BlockId,
    pub instruction: Option<usize>,
}

/// The two distinct evaluation points of a value-returning Invoke. Call
/// arguments are read before the instruction; normal block arguments are read
/// only after successful return, when that instruction's results exist.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SsaUseSite {
    BeforeInstruction { block: BlockId, instruction: usize },
    InvokeNormalEdge { block: BlockId },
}

impl SsaUseSite {
    #[must_use]
    pub fn block(self) -> BlockId {
        match self {
            Self::BeforeInstruction { block, .. } | Self::InvokeNormalEdge { block } => block,
        }
    }
}

impl DominatorTree {
    /// Compute dominance for `function` without recursing on the process stack.
    #[must_use]
    pub fn new(function: &Function) -> Self {
        compute_dominator_tree(function, None)
    }

    /// Whether the CFG was structurally usable for dominance analysis.
    #[must_use]
    pub fn is_well_formed(&self) -> bool {
        self.well_formed
    }

    /// Whether `block` is reachable from the function entry in a valid CFG.
    #[must_use]
    pub fn is_reachable(&self, block: BlockId) -> bool {
        self.well_formed && self.reachable.contains(&block.index())
    }

    /// The nearest strict dominator of a reachable block in a valid CFG.
    ///
    /// The entry has no immediate dominator, even when it has incoming loop
    /// edges. Invalid CFGs, missing blocks, and unreachable blocks return
    /// `None`. This reuses the map computed during construction; it performs
    /// one ordered-map lookup, not another traversal or dominance computation.
    #[must_use]
    pub fn immediate_dominator(&self, block: BlockId) -> Option<BlockId> {
        if !self.well_formed {
            return None;
        }
        self.immediate_dominator
            .get(&block.index())
            .copied()
            .map(BlockId::new)
    }

    /// Whether `dominator` strictly dominates `block` in a valid CFG.
    #[must_use]
    pub fn strictly_dominates(&self, dominator: BlockId, block: BlockId) -> bool {
        if !self.well_formed || dominator == block {
            return false;
        }
        let (Some(&dom_in), Some(&dom_out)) = (
            self.preorder.get(&dominator.index()),
            self.postorder.get(&dominator.index()),
        ) else {
            return false;
        };
        let (Some(&block_in), Some(&block_out)) = (
            self.preorder.get(&block.index()),
            self.postorder.get(&block.index()),
        ) else {
            return false;
        };
        dom_in < block_in && block_out < dom_out
    }

    /// Whether `dominator` dominates `block`, including block identity.
    #[must_use]
    pub fn dominates(&self, dominator: BlockId, block: BlockId) -> bool {
        self.is_reachable(block)
            && (dominator == block || self.strictly_dominates(dominator, block))
    }

    /// Existing dominator-tree tour interval, private to shared analyses.
    /// A reachable block is dominated by this block exactly when its entry
    /// number lies in this interval. Numbers are analysis-local, not evidence
    /// that can be transported across functions or mutations.
    pub(crate) fn dominance_interval(&self, block: BlockId) -> Option<(usize, usize)> {
        if !self.well_formed {
            return None;
        }
        Some((
            *self.preorder.get(&block.index())?,
            *self.postorder.get(&block.index())?,
        ))
    }

    /// Whether this exact successor edge occurs on every entry-to-`block`
    /// path. Successor indices are canonical terminator order: Br 0; CondBr
    /// then/else 0/1; Switch cases then default; Invoke normal/unwind 0/1.
    /// Parallel edges remain distinct. Unreachable or nonexistent uses fail.
    /// Construction stores only edges that dominate their own destination;
    /// each query uses ordered-map lookups, never another reachability walk.
    #[must_use]
    pub fn edge_dominates(&self, source: BlockId, successor: usize, block: BlockId) -> bool {
        self.dominating_edges
            .get(&(source.index(), successor))
            .is_some_and(|target| self.dominates(BlockId::new(*target), block))
    }

    /// Shared instruction/edge availability for an actual SSA definition.
    /// The containing module must separately validate unique definitions and
    /// operand/type bindings. This query validates coordinate bounds and the
    /// actual defining instruction's Invoke position, and grants no authority.
    #[must_use]
    pub fn definition_available_at(&self, definition: SsaDefinitionSite, site: SsaUseSite) -> bool {
        let use_block = site.block();
        if !self.is_reachable(use_block) {
            return false;
        }
        let Some(&definition_count) = self.instruction_counts.get(&definition.block.index()) else {
            return false;
        };
        if definition
            .instruction
            .is_some_and(|index| index >= definition_count)
        {
            return false;
        }
        let use_instruction = match site {
            SsaUseSite::BeforeInstruction { instruction, .. } => {
                if self
                    .instruction_counts
                    .get(&use_block.index())
                    .is_none_or(|count| instruction >= *count)
                {
                    return false;
                }
                instruction
            }
            SsaUseSite::InvokeNormalEdge { .. } => {
                let Some(&instruction) = self.invoke_instructions.get(&use_block.index()) else {
                    return false;
                };
                if definition.block == use_block && definition.instruction == Some(instruction) {
                    return true;
                }
                instruction
            }
        };
        if let Some(index) = definition.instruction
            && self.invoke_instructions.get(&definition.block.index()) == Some(&index)
        {
            return definition.block != use_block
                && self.edge_dominates(definition.block, 0, use_block);
        }
        if definition.block == use_block {
            definition
                .instruction
                .is_none_or(|index| index < use_instruction)
        } else {
            self.strictly_dominates(definition.block, use_block)
        }
    }
}

fn compute_dominator_tree(
    function: &Function,
    mut census: Option<&mut StaticFunctionPointerQueryCensus>,
) -> DominatorTree {
    let entry = function.entry.index();
    let mut block_ids = BTreeSet::new();
    for block in &function.blocks {
        if let Some(census) = census.as_deref_mut() {
            census.dominator_blocks_indexed += 1;
        }
        if !block_ids.insert(block.id.index()) {
            return DominatorTree::default();
        }
    }
    if !block_ids.contains(&entry) {
        return DominatorTree::default();
    }

    // Only a final terminator defines outgoing edges.  Reject malformed blocks
    // here instead of silently inventing a CFG that a transformation could use
    // to make invalid SSA appear valid.
    let mut successors = BTreeMap::<u32, Vec<u32>>::new();
    for block in &function.blocks {
        let mut terminator = None;
        for (instruction_index, node) in block.body.iter().enumerate() {
            if let Some(census) = census.as_deref_mut() {
                census.dominator_instructions_indexed += 1;
            }
            if node.is_terminator() {
                if instruction_index + 1 != block.body.len() || terminator.is_some() {
                    return DominatorTree::default();
                }
                terminator = Some(node);
            }
        }
        let Some(terminator) = terminator else {
            return DominatorTree::default();
        };
        let block_successors = terminator_successors(&terminator.inst);
        if let Some(census) = census.as_deref_mut() {
            census.dominator_edges_indexed += block_successors.len();
        }
        if block_successors
            .iter()
            .any(|successor| !block_ids.contains(successor))
        {
            return DominatorTree::default();
        }
        successors.insert(block.id.index(), block_successors);
    }

    // Iterative DFS postorder, reversed into RPO.  Mark on push so duplicate
    // edges cannot schedule duplicate frames.
    let mut reachable = BTreeSet::from([entry]);
    let mut postorder_walk = Vec::new();
    let mut dfs = vec![(entry, 0usize)];
    while let Some((block, next_successor)) = dfs.last_mut() {
        let successor = successors
            .get(block)
            .and_then(|items| items.get(*next_successor))
            .copied();
        match successor {
            Some(successor) => {
                *next_successor += 1;
                if reachable.insert(successor) {
                    dfs.push((successor, 0));
                }
            }
            None => {
                postorder_walk.push(*block);
                dfs.pop();
            }
        }
    }
    postorder_walk.reverse();
    let reverse_postorder = postorder_walk;
    let rpo_number: BTreeMap<u32, usize> = reverse_postorder
        .iter()
        .enumerate()
        .map(|(index, &block)| (block, index))
        .collect();

    let mut predecessors = BTreeMap::<u32, Vec<u32>>::new();
    for &block in &reverse_postorder {
        predecessors.entry(block).or_default();
    }
    for (&block, block_successors) in &successors {
        if !reachable.contains(&block) {
            continue;
        }
        for &successor in block_successors {
            if reachable.contains(&successor) {
                predecessors.entry(successor).or_default().push(block);
            }
        }
    }

    let mut immediate_dominator = BTreeMap::from([(entry, entry)]);
    let mut changed = true;
    while changed {
        changed = false;
        for &block in &reverse_postorder {
            if block == entry {
                continue;
            }
            let mut candidate = None;
            for &predecessor in &predecessors[&block] {
                if !immediate_dominator.contains_key(&predecessor) {
                    continue;
                }
                candidate = match candidate {
                    None => Some(predecessor),
                    Some(current) => {
                        intersect_idom(predecessor, current, &immediate_dominator, &rpo_number)
                    }
                };
                if candidate.is_none() {
                    return DominatorTree::default();
                }
            }
            if let Some(candidate) = candidate
                && immediate_dominator.get(&block) != Some(&candidate)
            {
                immediate_dominator.insert(block, candidate);
                changed = true;
            }
        }
    }
    if immediate_dominator.len() != reachable.len() {
        return DominatorTree::default();
    }

    let mut children = BTreeMap::<u32, Vec<u32>>::new();
    for (&block, &parent) in &immediate_dominator {
        if block != parent {
            children.entry(parent).or_default().push(block);
        }
    }
    for child_list in children.values_mut() {
        child_list.sort_by_key(|child| rpo_number.get(child).copied().unwrap_or(usize::MAX));
    }

    let mut preorder = BTreeMap::new();
    let mut postorder = BTreeMap::new();
    let mut timer = 0usize;
    preorder.insert(entry, timer);
    timer += 1;
    let mut tour = vec![(entry, 0usize)];
    while let Some((block, next_child)) = tour.last_mut() {
        let child = children
            .get(block)
            .and_then(|items| items.get(*next_child))
            .copied();
        match child {
            Some(child) => {
                *next_child += 1;
                if let Entry::Vacant(entry) = preorder.entry(child) {
                    entry.insert(timer);
                    timer += 1;
                    tour.push((child, 0));
                }
            }
            None => {
                postorder.insert(*block, timer);
                timer += 1;
                tour.pop();
            }
        }
    }
    if preorder.len() != reachable.len() || postorder.len() != reachable.len() {
        return DominatorTree::default();
    }

    // The fixed-point algorithm uses entry -> entry as a root sentinel, not
    // as a strict dominance fact. Retain the existing map without that sentinel
    // so consumers can traverse the real dominator tree without rebuilding it.
    immediate_dominator.remove(&entry);
    let mut result = DominatorTree {
        well_formed: true,
        reachable,
        immediate_dominator,
        preorder,
        postorder,
        instruction_counts: function
            .blocks
            .iter()
            .map(|block| (block.id.index(), block.body.len()))
            .collect(),
        // The terminators whose RESULTS are defined on their normal edge only:
        // `Invoke` and its indirect twin `InvokeIndirect` (amendment D, Part
        // 2). A result of either dominates a use only through edge 0.
        invoke_instructions: function
            .blocks
            .iter()
            .filter_map(|block| {
                matches!(
                    block.body.last()?.inst,
                    Inst::Invoke { .. } | Inst::InvokeIndirect { .. }
                )
                .then_some((block.id.index(), block.body.len() - 1))
            })
            .collect(),
        dominating_edges: BTreeMap::new(),
    };
    // An edge dominates its destination iff it is the unique reachable
    // incoming edge whose predecessor is NOT dominated by the destination.
    // Proof: the first visit to the destination cannot arrive from a dominated
    // predecessor (that would require an earlier visit). All other incoming
    // edges are backedges. Conversely, another non-dominated predecessor has
    // an entry path avoiding the destination, hence avoiding the named edge.
    // Count candidates in one edge pass, not one predecessor scan per edge.
    let mut entries = BTreeMap::<u32, Option<(u32, usize)>>::new();
    for (&source, targets) in &successors {
        if !result.is_reachable(BlockId::new(source)) {
            continue;
        }
        for (index, &target) in targets.iter().enumerate() {
            if target == entry || result.dominates(BlockId::new(target), BlockId::new(source)) {
                continue;
            }
            match entries.entry(target) {
                Entry::Vacant(slot) => {
                    slot.insert(Some((source, index)));
                }
                Entry::Occupied(mut slot) => {
                    slot.insert(None);
                }
            }
        }
    }
    for (target, edge) in entries {
        if let Some(edge) = edge {
            result.dominating_edges.insert(edge, target);
        }
    }
    result
}

fn terminator_successors(instruction: &Inst) -> Vec<u32> {
    // The exhaustive accessor: a new terminator cannot fall through to "no
    // successors" here (amendment D §1.3).
    instruction
        .successor_edges()
        .into_iter()
        .map(|edge| edge.target.index())
        .collect()
}

fn intersect_idom(
    mut left: u32,
    mut right: u32,
    immediate_dominator: &BTreeMap<u32, u32>,
    rpo_number: &BTreeMap<u32, usize>,
) -> Option<u32> {
    while left != right {
        let left_number = *rpo_number.get(&left)?;
        let right_number = *rpo_number.get(&right)?;
        if left_number > right_number {
            left = *immediate_dominator.get(&left)?;
        } else {
            right = *immediate_dominator.get(&right)?;
        }
    }
    Some(left)
}

/// Resolve one statically visible function pointer without retaining an index.
///
/// Consumers resolving multiple values in the same function should construct
/// one [`StaticFunctionPointerAnalysis`] instead of repeatedly calling this
/// convenience function.
#[must_use]
pub fn resolve_static_function_pointer(function: &Function, value: ValueId) -> Option<FuncId> {
    StaticFunctionPointerAnalysis::new(function).resolve(value)
}

// ---------------------------------------------------------------------------
// Indirect-call pools (spawn census, design 2026-09-29 §5.4)
//
// An indirect call's target is a value, so where `StaticFunctionPointerAnalysis`
// cannot resolve it exactly, the call is charged to every callable that could
// be that value: its POOL. The engine in `function_dependencies` turns the
// facts below into APPROX edges; this section owns the keys, the pool closure
// (membership, confinement, LIFETIME-ERASE and LAUNDER demotion, laundered
// data, upcast closure, open principals, unclosed pools) and the rule H
// summaries. The rules taken from trust-mc `kani_middle/dyn_universe.rs` are:
// upcasts merge pools; an upcast from a principal with no recorded member
// opens the target principal (UNKNOWN, never an empty pool); a function
// pointer stored in memory is a non-confined member. Two rules close what
// trust-mc leaves open: a principal some fact names but no member records is
// open whether or not it is upcast, and a pool is closed only while every
// callable could have come from a recorded CREATE (no UNKNOWN sink and no open
// principal stands for code that may have minted one).
// ---------------------------------------------------------------------------

/// Coarse ABI class of one argument position of a call shape.
///
/// Coarse on purpose: core itself transmutes between function-pointer types
/// whose arguments differ but are ABI-compatible (`library/core/src/fmt/rt.rs`),
/// so a class must never separate two types Rust lets one call through the
/// other. Every merge only adds pool members; a split would drop one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArgClass {
    /// Every thin pointer: raw, reference, box, `Rc`, function pointer, handle.
    ThinPointer,
    /// A fat pointer whose metadata is a length (`[T]`, `str`, `Arc<str>`).
    LengthFatPointer,
    /// A fat pointer whose metadata is a vtable word.
    VtableFatPointer,
    /// An integer of this many bits, signedness ignored (`bool` 8, `char` 32).
    Int(u32),
    /// A float of this many bits.
    Float(u32),
    /// Any other type proved not zero-sized, by a fingerprint of its exact
    /// type after repr-transparent peeling. A fingerprint collision merges
    /// two pools, never splits one.
    Exact(u64),
    /// Not classified, so it matches every class: a niche-optimized enum may
    /// be ABI-compatible with its payload, a target-free `usize` has no
    /// width, and any two zero-sized, 1-aligned types are ABI-compatible, so a
    /// type not proved non-zero-sized is never `Exact`.
    Unclassified,
}

impl ArgClass {
    fn matches(self, other: Self) -> bool {
        self == other || self == ArgClass::Unclassified || other == ArgClass::Unclassified
    }
}

/// The call shape a function-pointer pool (FnPool) is keyed by: an ABI
/// class, the C-variadic flag and one [`ArgClass`] per argument. Returns are
/// not part of the key (coarser is sound). A `None` component is one the
/// adapter could not state; it matches every value.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FnShape {
    /// Adapter-chosen ABI class. The trust-ir lane states none: its producer
    /// leaves function bodies at the default convention while it stamps
    /// `Rust` on fn-pointer calls, so a convention read from the module would
    /// split a pool. A call across conventions is UB (R4), so `None` is only
    /// coarser.
    pub abi: Option<u32>,
    pub variadic: Option<bool>,
    pub params: Option<Vec<ArgClass>>,
}

impl FnShape {
    /// The shape that matches every shape.
    #[must_use]
    pub fn unclassified() -> Self {
        Self::default()
    }

    /// Whether a call at one shape may reach a callable created at the other.
    #[must_use]
    pub fn matches(&self, other: &FnShape) -> bool {
        fn agree<T: PartialEq>(left: &Option<T>, right: &Option<T>) -> bool {
            match (left, right) {
                (Some(left), Some(right)) => left == right,
                _ => true,
            }
        }
        agree(&self.abi, &other.abi)
            && agree(&self.variadic, &other.variadic)
            && match (&self.params, &other.params) {
                (Some(left), Some(right)) => {
                    left.len() == right.len()
                        && left
                            .iter()
                            .zip(right)
                            .all(|(left, right)| left.matches(*right))
                }
                _ => true,
            }
    }
}

/// A trait-object principal. On the trust-ir lane it is the content-derived
/// [`FatPtrKind::TraitObject`] id, which covers the whole existential
/// predicate list, so `dyn Tr + Send` and `dyn Tr` are distinct principals
/// joined by an upcast fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PrincipalKey(pub u64);

/// A trait method, as the adapter identifies it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MethodKey(pub u64);

/// The key an indirect call is charged by.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PoolKey {
    /// FnPool: a call through a function pointer of this shape.
    Fn(FnShape),
    /// DynPool: a virtual call of `method` on a `dyn` value whose principal
    /// is `principal`. A vtable slot is filed under the principal of the
    /// unsize that minted it; upcast facts carry it to other principals.
    DynMethod {
        principal: PrincipalKey,
        method: MethodKey,
    },
    /// DynDropPool: `drop_in_place::<dyn principal>`.
    DynDrop(PrincipalKey),
}

impl PoolKey {
    /// The principal of a `dyn` key.
    #[must_use]
    pub fn principal(&self) -> Option<PrincipalKey> {
        match self {
            PoolKey::Fn(_) => None,
            PoolKey::DynMethod { principal, .. } | PoolKey::DynDrop(principal) => Some(*principal),
        }
    }

    fn with_principal(&self, principal: PrincipalKey) -> PoolKey {
        match self {
            PoolKey::Fn(shape) => PoolKey::Fn(shape.clone()),
            PoolKey::DynMethod { method, .. } => PoolKey::DynMethod {
                principal,
                method: *method,
            },
            PoolKey::DynDrop(_) => PoolKey::DynDrop(principal),
        }
    }
}

/// What a value passed to external code may carry: the rule H operand key.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CarriedKey {
    /// Exactly a callable of this key.
    Key(PoolKey),
    /// A `dyn` value of this principal: every method and the drop slot, and
    /// every principal an upcast can make of it.
    Principal(PrincipalKey),
    /// A function pointer of any shape.
    AnyFn,
    /// A `dyn` value of any principal.
    AnyDyn,
    /// Anything: an opaque value (a coroutine's saved state, a type the
    /// adapter cannot read) may lead to any callable.
    Any,
    /// An untyped pointer (`*const ()`, a pointer to a foreign type): it may
    /// lead to any callable but a CONFINED one. A confined member's erasure
    /// is a reference to a frame's local, and memory holding it is reached
    /// through a raw pointer only after a cast or raw pointer of a type that
    /// carries its principal, which demotes it (LIFETIME-ERASE). An adapter
    /// that confines nothing may use [`CarriedKey::Any`] instead.
    Untyped,
    /// Data whose type spells no callable (an integer, a float, a pointer to
    /// one). It holds what the census's LAUNDERs put there (`f as usize`
    /// handed to C, which calls it back): it admits exactly what the keys of
    /// every LAUNDER admit ([`ClosedPools::laundered_keys`]); before any
    /// LAUNDER, nothing. That is sound only while EVERY route by which a
    /// callable's bytes reach data (a value reinterpretation, a pointer view
    /// at another pointee, a union field, a reshaped fn pointer's parameter,
    /// an exposed address, a constant's bytes) is a recorded LAUNDER whose
    /// keys cover the callables those bytes may hold (spawn-census design
    /// 2026-09-29 §10, "typed LAUNDER"). A LAUNDER whose callables the adapter
    /// cannot name is a LAUNDER of [`CarriedKey::Any`].
    Laundered,
}

impl CarriedKey {
    /// The `dyn` principal this key names, if any.
    pub(crate) fn principal(&self) -> Option<PrincipalKey> {
        match self {
            CarriedKey::Principal(principal) => Some(*principal),
            CarriedKey::Key(key) => key.principal(),
            CarriedKey::AnyFn
            | CarriedKey::AnyDyn
            | CarriedKey::Any
            | CarriedKey::Untyped
            | CarriedKey::Laundered => None,
        }
    }

    /// Whether a value carrying this key may be a function pointer of some
    /// shape (it [admits](ClosedPools::admits) some FnPool key).
    fn may_be_fn(&self) -> bool {
        match self {
            CarriedKey::Key(PoolKey::Fn(_))
            | CarriedKey::AnyFn
            | CarriedKey::Any
            | CarriedKey::Untyped => true,
            CarriedKey::Key(_)
            | CarriedKey::Principal(_)
            | CarriedKey::AnyDyn
            | CarriedKey::Laundered => false,
        }
    }
}

/// One callable in one pool.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoolMember {
    pub member: ReachNode,
    pub key: PoolKey,
    /// Visible only to invoking sites in local bodies (design 2026-09-29 §5.4,
    /// confinement). Rule H charges the frames that hand it to external code.
    pub confined: bool,
}

/// One indirect call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PoolInvoke {
    pub node: ReachNode,
    pub key: PoolKey,
    /// What the call's operands carry. When a pool member is external code,
    /// the call hands these to it, and rule H applies as at a direct call.
    pub carried: Vec<CarriedKey>,
    pub site: ReachSite,
    pub via_drop: bool,
}

/// A local frame passing callable-carrying operands to external code (rule H).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PoolHandoff {
    pub node: ReachNode,
    pub callee: ReachNode,
    pub carried: Vec<CarriedKey>,
    pub site: ReachSite,
    pub via_drop: bool,
}

/// The indirect-call facts of one census graph, before closure.
#[derive(Debug, Clone, Default)]
pub(crate) struct IndirectCallUniverse {
    pub(crate) members: Vec<PoolMember>,
    pub(crate) invokes: Vec<PoolInvoke>,
    pub(crate) handoffs: Vec<PoolHandoff>,
    /// The first LAUNDER, the one a row cites for laundered data.
    pub(crate) launder: Option<ReachSite>,
    /// What data may hold: every LAUNDER's keys, each with the first LAUNDER
    /// that recorded it; never [`CarriedKey::Laundered`] itself.
    pub(crate) laundered: BTreeMap<CarriedKey, ReachSite>,
    pub(crate) erased: BTreeSet<PrincipalKey>,
    pub(crate) upcasts: BTreeSet<(PrincipalKey, PrincipalKey)>,
}

/// The pools after closure: what an invoking site may reach.
#[derive(Debug, Clone, Default)]
pub struct ClosedPools {
    members: Vec<PoolMember>,
    launder: Option<ReachSite>,
    /// What data ([`CarriedKey::Laundered`]) may hold: every LAUNDER's keys.
    laundered: BTreeMap<CarriedKey, ReachSite>,
    /// Whether some laundered key admits a FnPool key.
    laundered_fn: bool,
    open: BTreeSet<PrincipalKey>,
    unclosed: bool,
    /// For each principal, every other principal an upcast chain makes of it.
    upcast_reach: BTreeMap<PrincipalKey, BTreeSet<PrincipalKey>>,
}

impl IndirectCallUniverse {
    /// Every principal a fact names: invoked, carried to other code, or put
    /// into data by a LAUNDER.
    fn named_principals(&self) -> BTreeSet<PrincipalKey> {
        let carried = self
            .invokes
            .iter()
            .map(|invoke| &invoke.carried)
            .chain(self.handoffs.iter().map(|handoff| &handoff.carried))
            .flatten()
            .chain(self.laundered.keys())
            .filter_map(CarriedKey::principal);
        self.invokes
            .iter()
            .filter_map(|invoke| invoke.key.principal())
            .chain(carried)
            .collect()
    }

    /// Close the pools, in this order: upcast closure (members of a source
    /// principal join every principal an upcast chain reaches), demotion (a
    /// LAUNDER of [`CarriedKey::Any`] or [`CarriedKey::AnyDyn`] demotes every
    /// member, one of a key naming a principal demotes as a LIFETIME-ERASE of
    /// it does; a LIFETIME-ERASE of a principal demotes the members of it and
    /// of every principal an upcast makes of it), and
    /// open principals (a principal with no recorded member that a fact
    /// names, or that an upcast reaches from one with no recorded member,
    /// and everything it upcasts to). A LAUNDER leaves the FnPools keyed by
    /// shape ([`ClosedPools::pool`]). `unenumerated` says the graph holds an UNKNOWN sink: code or
    /// data the adapter could not enumerate, which may have minted any
    /// callable, so then no pool is closed; nor is any while a principal is
    /// open.
    #[must_use]
    pub(crate) fn close(&self, unenumerated: bool) -> ClosedPools {
        let mut adjacency: BTreeMap<PrincipalKey, BTreeSet<PrincipalKey>> = BTreeMap::new();
        for (from, to) in &self.upcasts {
            if from != to {
                adjacency.entry(*from).or_default().insert(*to);
            }
        }
        let mut upcast_reach: BTreeMap<PrincipalKey, BTreeSet<PrincipalKey>> = BTreeMap::new();
        for start in adjacency.keys() {
            let mut reached = BTreeSet::new();
            let mut pending: Vec<PrincipalKey> = adjacency[start].iter().copied().collect();
            while let Some(next) = pending.pop() {
                if reached.insert(next)
                    && let Some(targets) = adjacency.get(&next)
                {
                    pending.extend(targets.iter().copied());
                }
            }
            reached.remove(start);
            upcast_reach.insert(*start, reached);
        }
        let closure_of = |seeds: &BTreeSet<PrincipalKey>| {
            let mut closed = seeds.clone();
            for seed in seeds {
                if let Some(reached) = upcast_reach.get(seed) {
                    closed.extend(reached.iter().copied());
                }
            }
            closed
        };
        // A LAUNDER of a callable the adapter cannot name may put a confined
        // erasure into data; a keyed one demotes the principals it names. A
        // LAUNDER of fn keys demotes nothing: a confined member is a vtable
        // slot, which data holds only through a key of its principal.
        let launders_any_dyn = self
            .laundered
            .keys()
            .any(|key| matches!(key, CarriedKey::Any | CarriedKey::AnyDyn));
        let mut erased = self.erased.clone();
        erased.extend(self.laundered.keys().filter_map(CarriedKey::principal));
        let demoted = closure_of(&erased);

        // One row per (member, key); a row is confined only if every fact
        // filing it there says so.
        let mut rows: BTreeMap<(ReachNode, PoolKey), bool> = BTreeMap::new();
        let mut file = |member: ReachNode, key: PoolKey, confined: bool| {
            let confined = confined
                && !launders_any_dyn
                && key
                    .principal()
                    .is_none_or(|principal| !demoted.contains(&principal));
            rows.entry((member, key))
                .and_modify(|row| *row &= confined)
                .or_insert(confined);
        };
        for fact in &self.members {
            file(fact.member, fact.key.clone(), fact.confined);
            if let Some(principal) = fact.key.principal()
                && let Some(reached) = upcast_reach.get(&principal)
            {
                for target in reached {
                    file(fact.member, fact.key.with_principal(*target), fact.confined);
                }
            }
        }
        let members: Vec<PoolMember> = rows
            .into_iter()
            .map(|((member, key), confined)| PoolMember {
                member,
                key,
                confined,
            })
            .collect();

        let recorded: BTreeSet<PrincipalKey> = members
            .iter()
            .filter_map(|row| row.key.principal())
            .collect();
        let opened: BTreeSet<PrincipalKey> = self
            .upcasts
            .iter()
            .filter(|(from, to)| from != to && !recorded.contains(from))
            .map(|(_, to)| *to)
            .chain(
                self.named_principals()
                    .into_iter()
                    .filter(|principal| !recorded.contains(principal)),
            )
            .collect();
        let open = closure_of(&opened);
        ClosedPools {
            unclosed: unenumerated || !open.is_empty(),
            open,
            members,
            launder: self.launder,
            laundered_fn: self.laundered.keys().any(CarriedKey::may_be_fn),
            laundered: self.laundered.clone(),
            upcast_reach,
        }
    }
}

impl ClosedPools {
    /// Exact closure of an empty universe: no membership, handoff, laundering,
    /// erasure or upcast work exists. Preserve the adapter's unenumerated sink.
    pub(crate) fn empty_with_unenumerated(unenumerated: bool) -> Self {
        Self {
            unclosed: unenumerated,
            ..Self::default()
        }
    }

    /// Every member after closure, with its effective confinement.
    #[must_use]
    pub fn members(&self) -> &[PoolMember] {
        &self.members
    }

    /// Whether a LAUNDER turned a callable into plain data: then data
    /// ([`CarriedKey::Laundered`]) may carry what its keys admit
    /// ([`Self::laundered_keys`]). The FnPools stay keyed by shape
    /// ([`Self::pool`]).
    #[must_use]
    pub fn laundered(&self) -> bool {
        !self.laundered.is_empty()
    }

    /// What data may hold, each key with the first LAUNDER that recorded it:
    /// [`CarriedKey::Laundered`] admits what these admit.
    #[must_use]
    pub fn laundered_keys(&self) -> &BTreeMap<CarriedKey, ReachSite> {
        &self.laundered
    }

    /// The first LAUNDER.
    #[must_use]
    pub fn launder_site(&self) -> Option<ReachSite> {
        self.launder
    }

    /// Principals whose runtime types are not all recorded.
    #[must_use]
    pub fn open_principals(&self) -> &BTreeSet<PrincipalKey> {
        &self.open
    }

    /// Whether code the census did not enumerate (an UNKNOWN sink, or an open
    /// principal's unrecorded runtime types) may have minted a callable no
    /// CREATE records. Then no pool is closed: every invoke also reaches an
    /// UNKNOWN(`UnclosedPool`) sink, and so does every hand-off whose operands
    /// may carry a callable the callee invokes.
    #[must_use]
    pub fn unclosed(&self) -> bool {
        self.unclosed
    }

    /// The members an invoke at `key` may reach, confined ones included.
    ///
    /// An fn invoke reaches the members whose shape matches its own, whether
    /// or not a LAUNDER turned some callable into data and back. A member is
    /// filed under its own signature's shape (a reification's or closure
    /// coercion's target, an allocation's or export's instance signature;
    /// an unclassified shape where the adapter cannot state it), and a call
    /// through a function pointer whose type is not ABI-compatible with the
    /// callee's signature is undefined behaviour (R4). The shapes are closed
    /// under the std `fn` ABI-compatibility rules ([`ArgClass`]: integer
    /// classes ignore signedness, every thin pointer is one class, a type not
    /// proved non-zero-sized is unclassified, and the ABI ignores `-unwind`),
    /// so every compatible pair matches: a callable laundered to an integer,
    /// a raw pointer or another fn type, then called, is called at a shape
    /// its own pool's key matches, or the program has UB. This is the
    /// argument that already keeps a pointee reinterpretation (a fn pointer
    /// read back through another pointee type) from being a LAUNDER.
    pub fn pool<'pools>(
        &'pools self,
        key: &'pools PoolKey,
    ) -> impl Iterator<Item = &'pools PoolMember> + 'pools {
        self.members
            .iter()
            .filter(move |row| self.in_pool(key, row))
    }

    /// Whether an invoke at `key` may reach the member `row` ([`Self::pool`]).
    pub(crate) fn in_pool(&self, key: &PoolKey, row: &PoolMember) -> bool {
        match (key, &row.key) {
            (PoolKey::Fn(call), PoolKey::Fn(created)) => call.matches(created),
            (invoked, filed) => invoked == filed,
        }
    }

    /// Whether `key`'s pool may hold a callable no fact records: every pool
    /// while the pools are [unclosed](Self::unclosed), else an open
    /// principal's.
    #[must_use]
    pub fn is_open(&self, key: &PoolKey) -> bool {
        self.unclosed
            || key
                .principal()
                .is_some_and(|principal| self.open.contains(&principal))
    }

    fn principal_reaches(&self, from: PrincipalKey, to: PrincipalKey) -> bool {
        from == to
            || self
                .upcast_reach
                .get(&from)
                .is_some_and(|reached| reached.contains(&to))
    }

    /// Whether a value carrying `carried` may be what an invoke at `key` calls.
    pub(crate) fn admits(&self, carried: &CarriedKey, key: &PoolKey) -> bool {
        match (carried, key) {
            (CarriedKey::Any | CarriedKey::Untyped, _)
            | (CarriedKey::AnyFn, PoolKey::Fn(_))
            | (CarriedKey::AnyDyn, PoolKey::DynMethod { .. } | PoolKey::DynDrop(_)) => true,
            // Data holds what the LAUNDERs' keys admit. A fn key is admitted
            // when some laundered key admits any fn key: shape matching is
            // not transitive (an unclassified class matches both of two
            // classes that do not match each other), so a callable a laundered
            // key admits may be what an invoke of a key that key does not
            // admit calls. Which members data holds is `may_hold`'s.
            (CarriedKey::Laundered, PoolKey::Fn(_)) => self.laundered_fn,
            // `laundered` never holds `Laundered`, so this recursion is one
            // level deep.
            (CarriedKey::Laundered, key) => {
                self.laundered.keys().any(|held| self.admits(held, key))
            }
            (CarriedKey::AnyFn, _) | (CarriedKey::AnyDyn, PoolKey::Fn(_)) => false,
            // Called at another shape it is not ABI-compatible with: UB (R4),
            // as for an invoke ([`Self::pool`]).
            (CarriedKey::Key(PoolKey::Fn(held)), PoolKey::Fn(called)) => held.matches(called),
            (CarriedKey::Key(PoolKey::Fn(_)), _) => false,
            (CarriedKey::Principal(held), key) => key
                .principal()
                .is_some_and(|called| self.principal_reaches(*held, called)),
            (CarriedKey::Key(held), key) => match (held.principal(), key.principal()) {
                (Some(from), Some(to)) => {
                    self.principal_reaches(from, to) && held.with_principal(to) == *key
                }
                _ => false,
            },
        }
    }

    /// Whether a value carrying `carried` may be a `dyn` value of `principal`.
    pub(crate) fn admits_principal(&self, carried: &CarriedKey, principal: PrincipalKey) -> bool {
        match carried {
            CarriedKey::Any | CarriedKey::Untyped | CarriedKey::AnyDyn => true,
            CarriedKey::Laundered => self
                .laundered
                .keys()
                .any(|held| self.admits_principal(held, principal)),
            CarriedKey::AnyFn => false,
            CarriedKey::Principal(held) => self.principal_reaches(*held, principal),
            CarriedKey::Key(held) => held
                .principal()
                .is_some_and(|held| self.principal_reaches(held, principal)),
        }
    }

    /// Whether a value carrying `carried` may be some callable: true for
    /// every key but [`CarriedKey::Laundered`] before any LAUNDER.
    pub(crate) fn may_carry_callable(&self, carried: &CarriedKey) -> bool {
        *carried != CarriedKey::Laundered || self.laundered()
    }

    /// Whether a value carrying `carried`, which [`Self::admits`] an invoke's
    /// key, may hold `member` of that key's pool: an untyped pointer never
    /// leads to a confined member ([`CarriedKey::Untyped`]); data holds a
    /// member only if some laundered key admits the member's own key and may
    /// hold it; every other key may hold every member its key admits.
    pub(crate) fn may_hold(&self, carried: &CarriedKey, member: &PoolMember) -> bool {
        match carried {
            CarriedKey::Untyped => !member.confined,
            // `laundered` never holds `Laundered`: one level deep.
            CarriedKey::Laundered => self
                .laundered
                .keys()
                .any(|held| self.admits(held, &member.key) && self.may_hold(held, member)),
            CarriedKey::Key(_)
            | CarriedKey::Principal(_)
            | CarriedKey::AnyFn
            | CarriedKey::AnyDyn
            | CarriedKey::Any => true,
        }
    }
}

/// What a node's forward closure (its Run and Approx edges) may invoke: the
/// rule H summary of one node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InvokedKeys {
    /// The closure holds code that is not enumerated (an opaque body or an
    /// UNKNOWN sink), so it may invoke any key: absent is never quiet.
    Every,
    /// Indices of the invoke facts the closure contains.
    Some(BTreeSet<usize>),
}

/// Rule H summaries for every node: a forward fixpoint over the strongly
/// connected components of `successors`, bottom-up, with no budget.
pub(crate) struct InvokedKeySummaries {
    component: Vec<usize>,
    summaries: Vec<InvokedKeys>,
}

impl InvokedKeySummaries {
    /// `successors[n]` are the Run and Approx successors of node `n`;
    /// `own[n]` the invoke facts at `n`; `everything[n]` marks a node whose
    /// behaviour is not enumerated.
    pub(crate) fn new(successors: &[Vec<usize>], own: &[Vec<usize>], everything: &[bool]) -> Self {
        let count = successors.len();
        const UNVISITED: usize = usize::MAX;
        let mut index = vec![UNVISITED; count];
        let mut low = vec![0; count];
        let mut on_stack = vec![false; count];
        let mut stack: Vec<usize> = Vec::new();
        let mut component = vec![UNVISITED; count];
        let mut summaries: Vec<InvokedKeys> = Vec::new();
        let mut next = 0;
        for root in 0..count {
            if index[root] != UNVISITED {
                continue;
            }
            // Iterative Tarjan: (node, next successor position).
            let mut calls: Vec<(usize, usize)> = vec![(root, 0)];
            index[root] = next;
            low[root] = next;
            next += 1;
            stack.push(root);
            on_stack[root] = true;
            while let Some(&(node, position)) = calls.last() {
                if let Some(&successor) = successors[node].get(position) {
                    if let Some(frame) = calls.last_mut() {
                        frame.1 += 1;
                    }
                    if index[successor] == UNVISITED {
                        index[successor] = next;
                        low[successor] = next;
                        next += 1;
                        stack.push(successor);
                        on_stack[successor] = true;
                        calls.push((successor, 0));
                    } else if on_stack[successor] {
                        low[node] = low[node].min(index[successor]);
                    }
                    continue;
                }
                calls.pop();
                if let Some(&(parent, _)) = calls.last() {
                    low[parent] = low[parent].min(low[node]);
                }
                if low[node] != index[node] {
                    continue;
                }
                // Tarjan emits a component after every component it reaches,
                // so each successor component's summary is already final.
                let id = summaries.len();
                let mut members = Vec::new();
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    component[member] = id;
                    members.push(member);
                    if member == node {
                        break;
                    }
                }
                let mut every = false;
                let mut keys = BTreeSet::new();
                for &member in &members {
                    every |= everything[member];
                    keys.extend(own[member].iter().copied());
                    for &successor in &successors[member] {
                        match &summaries.get(component[successor]) {
                            Some(InvokedKeys::Every) => every = true,
                            Some(InvokedKeys::Some(reached)) => {
                                keys.extend(reached.iter().copied())
                            }
                            // Same component (not yet pushed).
                            None => {}
                        }
                    }
                }
                summaries.push(if every {
                    InvokedKeys::Every
                } else {
                    InvokedKeys::Some(keys)
                });
            }
        }
        Self {
            component,
            summaries,
        }
    }

    pub(crate) fn of(&self, node: usize) -> &InvokedKeys {
        &self.summaries[self.component[node]]
    }

    /// The strongly connected component holding `node`: nodes of one
    /// component share one summary.
    pub(crate) fn component(&self, node: usize) -> usize {
        self.component[node]
    }
}

// --- trust-ir lane keys ----------------------------------------------------

/// The FnPool shape of a trust-ir signature. It states no ABI class (see
/// [`FnShape::abi`]). A missing signature is unclassified.
pub(crate) fn fn_pool_shape(module: &Module, signature: FuncTyId) -> FnShape {
    let Some(signature) = module.func_types.get(signature.as_usize()) else {
        return FnShape::unclassified();
    };
    FnShape {
        abi: None,
        variadic: Some(signature.is_vararg),
        params: Some(
            signature
                .params
                .iter()
                .map(|ty| arg_class(module, ty, 0))
                .collect(),
        ),
    }
}

fn fingerprint(ty: &Ty) -> u64 {
    let mut hasher = DefaultHasher::new();
    ty.hash(&mut hasher);
    hasher.finish()
}

/// A bound on a malformed module's cyclic table chains.
fn depth_bound(module: &Module) -> usize {
    module.types.len() + module.structs.len() + module.records.len() + module.closure_types.len()
}

/// One argument's class, syntactically and without layouts. `depth` bounds
/// a malformed module's cyclic transparent or refinement chain.
fn arg_class(module: &Module, ty: &Ty, depth: usize) -> ArgClass {
    if depth > depth_bound(module) {
        return ArgClass::Unclassified;
    }
    // Any two zero-sized, 1-aligned types are ABI-compatible (std `fn` docs),
    // so only a type proved not zero-sized gets a class of its own.
    let exact = || match zero_sized(module, ty, depth) {
        Some(false) => ArgClass::Exact(fingerprint(ty)),
        Some(true) | None => ArgClass::Unclassified,
    };
    match ty {
        Ty::Storage(_) => ArgClass::Unclassified,
        Ty::I8 | Ty::U8 | Ty::Bool => ArgClass::Int(8),
        Ty::I16 | Ty::U16 => ArgClass::Int(16),
        Ty::I32 | Ty::U32 | Ty::Char => ArgClass::Int(32),
        Ty::I64 | Ty::U64 => ArgClass::Int(64),
        Ty::I128 | Ty::U128 => ArgClass::Int(128),
        Ty::Isize | Ty::Usize => module
            .target_info
            .as_ref()
            .and_then(|target| target.pointer_size.checked_mul(8))
            .map_or(ArgClass::Unclassified, ArgClass::Int),
        Ty::F16 => ArgClass::Float(16),
        Ty::F32 => ArgClass::Float(32),
        Ty::F64 => ArgClass::Float(64),
        Ty::Ptr
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Func(_)
        | Ty::Handle(_) => ArgClass::ThinPointer,
        Ty::FatPtr(FatPtrKind::Slice(_) | FatPtrKind::Str | FatPtrKind::ContainerLen) => {
            ArgClass::LengthFatPointer
        }
        Ty::FatPtr(FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable) => {
            ArgClass::VtableFatPointer
        }
        Ty::Refine(base, _) => module
            .types
            .get(base.as_usize())
            .map_or(ArgClass::Unclassified, |base| {
                arg_class(module, base, depth + 1)
            }),
        Ty::Struct(id) => {
            let mut definitions = module.structs.iter().filter(|def| def.id == *id);
            let (Some(definition), None) = (definitions.next(), definitions.next()) else {
                return ArgClass::Unclassified;
            };
            if definition.repr != StructRepr::Transparent {
                return exact();
            }
            let mut payload = definition
                .fields
                .iter()
                .filter(|field| zero_sized(module, &field.ty, depth + 1) != Some(true));
            match (payload.next(), payload.next()) {
                (Some(field), None) => arg_class(module, &field.ty, depth + 1),
                _ => ArgClass::Unclassified,
            }
        }
        Ty::Tuple(_)
        | Ty::Array(..)
        | Ty::Vector(..)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Sequence(_)
        | Ty::Set(..)
        | Ty::Tensor(..) => exact(),
        Ty::Enum(_) | Ty::Unit | Ty::Never | Ty::Dialect(_) | Ty::Error => ArgClass::Unclassified,
        Ty::Ext(e) => e.unreachable(),
    }
}

/// Whether `ty` is zero-sized, by its spelling or its declared size: `None`
/// when neither decides it (never read as "not zero-sized").
fn zero_sized(module: &Module, ty: &Ty, depth: usize) -> Option<bool> {
    if depth > depth_bound(module) {
        return None;
    }
    // Zero-sized when every part is; not when any part is not.
    fn all<'a>(
        module: &Module,
        parts: impl IntoIterator<Item = &'a Ty>,
        depth: usize,
    ) -> Option<bool> {
        let mut decided = Some(true);
        for part in parts {
            match zero_sized(module, part, depth + 1) {
                Some(true) => {}
                Some(false) => return Some(false),
                None => decided = None,
            }
        }
        decided
    }
    match ty {
        Ty::Storage(layout) => layout
            .is_well_formed(module.pointer_bits())
            .then_some(layout.size_bytes == 0),
        Ty::Unit | Ty::Never => Some(true),
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
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Func(_)
        | Ty::Handle(_)
        | Ty::FatPtr(_) => Some(false),
        Ty::Vector(_, lanes) => (*lanes > 0).then_some(false),
        Ty::Array(_, 0) => Some(true),
        Ty::Array(element, _) | Ty::Refine(element, _) => module
            .types
            .get(element.as_usize())
            .and_then(|element| zero_sized(module, element, depth + 1)),
        Ty::Tuple(fields) => all(module, fields, depth),
        Ty::Struct(id) => {
            let mut definitions = module.structs.iter().filter(|def| def.id == *id);
            match (definitions.next(), definitions.next()) {
                (Some(definition), None) => match definition.size {
                    Some(size) => Some(size == 0),
                    None => all(
                        module,
                        definition.fields.iter().map(|field| &field.ty),
                        depth,
                    ),
                },
                _ => None,
            }
        }
        Ty::Record(id) => {
            let mut definitions = module.records.iter().filter(|def| def.id == *id);
            match (definitions.next(), definitions.next()) {
                (Some(definition), None) => all(
                    module,
                    definition.fields.iter().map(|field| &field.ty),
                    depth,
                ),
                _ => None,
            }
        }
        // A closure value names its function as well as its captures.
        Ty::Closure(_)
        | Ty::Enum(_)
        | Ty::Sequence(_)
        | Ty::Set(..)
        | Ty::Tensor(..)
        | Ty::Dialect(_)
        | Ty::Error => None,
        Ty::Ext(e) => e.unreachable(),
    }
}

/// The rule H operand keys of a trust-ir type: what a value of it may carry.
/// Any value with data may also hold a laundered callable
/// ([`CarriedKey::Laundered`]). `defs` is the pass's all-definitions index
/// over `module` ([`Module::callable_carriers`]).
pub(crate) fn carried_keys(
    module: &Module,
    defs: &mut crate::reach::DefIndex,
    ty: &Ty,
) -> Vec<CarriedKey> {
    let carriers = module.callable_carriers_in(defs, ty);
    if carriers.opaque {
        return vec![CarriedKey::Any];
    }
    let mut keys: Vec<CarriedKey> = carriers
        .fn_types
        .iter()
        .map(|signature| CarriedKey::Key(PoolKey::Fn(fn_pool_shape(module, *signature))))
        .collect();
    for closure in &carriers.closures {
        keys.push(match module.closure_types.get(closure.as_usize()) {
            Some(closure) => CarriedKey::Key(PoolKey::Fn(fn_pool_shape(module, closure.func))),
            None => CarriedKey::AnyFn,
        });
    }
    keys.extend(
        carriers
            .principals
            .iter()
            .map(|principal| CarriedKey::Principal(PrincipalKey(u64::from(*principal)))),
    );
    if carriers.erased_dyn {
        keys.push(CarriedKey::AnyDyn);
    }
    if zero_sized(module, ty, 0) != Some(true) {
        keys.push(CarriedKey::Laundered);
    }
    keys
}

/// LAUNDER on the trust-ir lane: a transmute or pointer cast that changes a
/// type carrying a callable (design 2026-09-29 §5.4).
pub(crate) fn cast_launders(
    nominal: &NominalTypeReachability<'_>,
    op: CastOp,
    src: &Ty,
    dst: &Ty,
) -> bool {
    let reinterprets = match op {
        CastOp::Transmute
        | CastOp::Bitcast
        | CastOp::PtrToInt
        | CastOp::IntToPtr
        | CastOp::PtrToPtr => true,
        // `ReifyFnPointer` keeps the callable's identity: the constant it
        // casts is the CREATE. The rest convert scalars.
        CastOp::ReifyFnPointer
        | CastOp::Trunc
        | CastOp::ZExt
        | CastOp::SExt
        | CastOp::FPTrunc
        | CastOp::FPExt
        | CastOp::FPToUI
        | CastOp::FPToSI
        | CastOp::UIToFP
        | CastOp::SIToFP
        | CastOp::FPToSISat
        | CastOp::FPToUISat => false,
    };
    reinterprets && src != dst && (nominal.contains_callable(src) || nominal.contains_callable(dst))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::Ty;
    use crate::value::{BlockId, FuncTyId};
    use crate::{Block, CallingConv, Function, InstrNode};

    fn function(nodes: Vec<InstrNode>) -> Function {
        let mut function =
            Function::new(FuncId::new(0), "caller", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body = nodes;
        function.blocks.push(block);
        function
    }

    fn fn_def(result: u32, target: u32) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::Func(FuncTyId::new(0)),
            value: Constant::FnDef(FuncId::new(target)),
        })
        .with_result(ValueId::new(result))
    }

    fn copy(result: u32, operand: u32) -> InstrNode {
        InstrNode::new(Inst::Copy {
            ty: Ty::Func(FuncTyId::new(0)),
            operand: ValueId::new(operand),
        })
        .with_result(ValueId::new(result))
    }

    fn reify_to_pointer(result: u32, operand: u32) -> InstrNode {
        InstrNode::new(Inst::Cast {
            op: CastOp::ReifyFnPointer,
            src_ty: Ty::Func(FuncTyId::new(0)),
            dst_ty: Ty::Ptr,
            operand: ValueId::new(operand),
        })
        .with_result(ValueId::new(result))
    }

    fn indirect_call(callee: u32) -> InstrNode {
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(callee),
            sig: FuncTyId::new(0),
            args: Vec::new(),
            calling_conv: CallingConv::C,
        })
    }

    fn return_void() -> InstrNode {
        InstrNode::new(Inst::Return { values: Vec::new() })
    }

    #[test]
    fn resolves_direct_and_copy_reify_chains() {
        let function = function(vec![
            fn_def(0, 7),
            copy(1, 0),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(FuncTyId::new(0)),
                dst_ty: Ty::Func(FuncTyId::new(0)),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
        ]);
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        assert_eq!(
            analysis.cache_state(),
            StaticFunctionPointerCacheState::default()
        );
        assert!(analysis.definitions.get().is_none());
        assert!(analysis.dominators.get().is_none());
        assert_eq!(analysis.resolve(ValueId::new(0)), Some(FuncId::new(7)));
        assert_eq!(analysis.resolve(ValueId::new(2)), Some(FuncId::new(7)));
        assert!(analysis.definitions.get().is_some());
        assert!(analysis.dominators.get().is_none());
        assert_eq!(
            analysis.cache_state(),
            StaticFunctionPointerCacheState {
                use_site_index_built: false,
                definition_index_built: true,
                provenance_index_built: false,
                dominator_tree_built: false,
            }
        );
    }

    #[test]
    fn legitimate_long_chains_have_no_arbitrary_depth_limit() {
        let mut nodes = vec![fn_def(0, 11)];
        for result in 1..=128 {
            nodes.push(copy(result, result - 1));
        }
        let function = function(nodes);

        assert_eq!(
            resolve_static_function_pointer(&function, ValueId::new(128)),
            Some(FuncId::new(11))
        );
    }

    #[test]
    fn dynamic_ambiguous_and_cyclic_values_fail_closed() {
        let dynamic = function(vec![
            InstrNode::new(Inst::NullPtr).with_result(ValueId::new(0)),
        ]);
        assert_eq!(
            resolve_static_function_pointer(&dynamic, ValueId::new(0)),
            None
        );

        let duplicate = function(vec![fn_def(0, 1), fn_def(0, 2)]);
        assert_eq!(
            resolve_static_function_pointer(&duplicate, ValueId::new(0)),
            None
        );

        let mut block_parameter_conflict = function(vec![fn_def(0, 3)]);
        block_parameter_conflict.blocks[0]
            .params
            .push((ValueId::new(0), Ty::Func(FuncTyId::new(0))));
        assert_eq!(
            resolve_static_function_pointer(&block_parameter_conflict, ValueId::new(0)),
            None
        );

        let multiple_results = function(vec![fn_def(0, 4).with_result(ValueId::new(1))]);
        assert_eq!(
            resolve_static_function_pointer(&multiple_results, ValueId::new(0)),
            None
        );

        let cyclic = function(vec![copy(0, 1), copy(1, 0)]);
        assert_eq!(
            resolve_static_function_pointer(&cyclic, ValueId::new(0)),
            None
        );
    }

    #[test]
    fn typed_resolution_accepts_exact_dominating_chain() {
        let function = function(vec![
            fn_def(0, 7),
            copy(1, 0),
            reify_to_pointer(2, 1),
            indirect_call(2),
            return_void(),
        ]);
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        let resolution = analysis
            .resolve_typed_at(ValueId::new(2), BlockId::new(0), 3)
            .expect("the exact dominating chain is static");
        assert_eq!(resolution.containing_function(), FuncId::new(0));
        assert_eq!(resolution.function(), FuncId::new(7));
        assert_eq!(resolution.declared_signature(), FuncTyId::new(0));
        assert_eq!(resolution.carrier(), StaticFunctionPointerCarrier::Pointer);
        assert_eq!(resolution.queried_value(), ValueId::new(2));
        assert_eq!(resolution.use_block(), BlockId::new(0));
        assert_eq!(resolution.use_instruction_index(), 3);
        assert_eq!(resolution.origin_value(), ValueId::new(0));
        assert_eq!(resolution.origin_block(), BlockId::new(0));
        assert_eq!(resolution.origin_instruction_index(), 0);
        assert_eq!(resolution.chain_definitions(), 3);
        assert!(analysis.definitions.get().is_some());
        assert!(analysis.provenances.get().is_some());
        assert!(analysis.dominators.get().is_some());
    }

    #[test]
    fn typed_use_block_parameter_keeps_whole_function_state_lazy() {
        let mut function = function(vec![indirect_call(0), return_void()]);
        function.blocks[0]
            .params
            .push((ValueId::new(0), Ty::Func(FuncTyId::new(0))));
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        assert!(analysis.definitions.get().is_none());
        assert!(analysis.provenances.get().is_none());
        assert!(analysis.dominators.get().is_none());
        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(0), BlockId::new(0), 0),
            None
        );
        assert!(analysis.definitions.get().is_none());
        assert!(analysis.provenances.get().is_none());
        assert!(analysis.dominators.get().is_none());
        assert_eq!(
            analysis.cache_state(),
            StaticFunctionPointerCacheState {
                use_site_index_built: true,
                definition_index_built: false,
                provenance_index_built: false,
                dominator_tree_built: false,
            }
        );
        let (resolution, census) =
            analysis.resolve_typed_at_with_census(ValueId::new(0), BlockId::new(0), 0);
        assert_eq!(resolution, None);
        assert_eq!(
            census,
            StaticFunctionPointerQueryCensus {
                exact_use_operands_visited: 1,
                ..StaticFunctionPointerQueryCensus::default()
            }
        );
    }

    #[test]
    fn exact_callee_authentication_short_circuits_high_arity_operands() {
        let mut function = function(vec![
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: FuncTyId::new(0),
                args: (1..=4_096).map(ValueId::new).collect(),
                calling_conv: CallingConv::C,
            }),
            return_void(),
        ]);
        function.blocks[0]
            .params
            .push((ValueId::new(0), Ty::Func(FuncTyId::new(0))));
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        let (resolution, census) =
            analysis.resolve_typed_at_with_census(ValueId::new(0), BlockId::new(0), 0);
        assert_eq!(resolution, None);
        assert_eq!(census.exact_use_operands_visited, 1);
        assert_eq!(census.prefilter_instructions_visited, 0);
        assert_eq!(
            analysis.cache_state(),
            StaticFunctionPointerCacheState {
                use_site_index_built: true,
                definition_index_built: false,
                provenance_index_built: false,
                dominator_tree_built: false,
            }
        );
    }

    #[test]
    fn typed_local_noncandidate_keeps_whole_function_state_lazy() {
        let function = function(vec![
            InstrNode::new(Inst::NullPtr).with_result(ValueId::new(0)),
            indirect_call(0),
            return_void(),
        ]);
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        assert!(analysis.definitions.get().is_none());
        assert!(analysis.provenances.get().is_none());
        assert!(analysis.dominators.get().is_none());
        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(0), BlockId::new(0), 1),
            None
        );
        assert!(analysis.definitions.get().is_none());
        assert!(analysis.provenances.get().is_none());
        assert!(analysis.dominators.get().is_none());
    }

    #[test]
    fn many_blocks_parameters_and_dynamic_calls_build_use_metadata_once() {
        const BLOCK_COUNT: u32 = 257;
        const PARAMETER_COUNT: u32 = 512;

        let use_block_id = BlockId::new(BLOCK_COUNT - 1);
        let mut function = Function::new(
            FuncId::new(0),
            "many_dynamic_calls",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        for block_index in 0..BLOCK_COUNT - 1 {
            let mut block = Block::new(BlockId::new(block_index));
            block.body.push(return_void());
            function.blocks.push(block);
        }
        let mut use_block = Block::new(use_block_id);
        for parameter in 0..PARAMETER_COUNT {
            use_block
                .params
                .push((ValueId::new(parameter), Ty::Func(FuncTyId::new(0))));
            use_block.body.push(indirect_call(parameter));
        }
        use_block.body.push(return_void());
        function.blocks.push(use_block);

        let analysis = StaticFunctionPointerAnalysis::new(&function);
        for parameter in 0..PARAMETER_COUNT {
            let (resolution, census) = analysis.resolve_typed_at_with_census(
                ValueId::new(parameter),
                use_block_id,
                parameter as usize,
            );
            assert_eq!(resolution, None);
            if parameter == 0 {
                assert_eq!(
                    census,
                    StaticFunctionPointerQueryCensus {
                        use_site_blocks_indexed: BLOCK_COUNT as usize,
                        use_site_parameters_indexed: PARAMETER_COUNT as usize,
                        exact_use_operands_visited: 1,
                        ..StaticFunctionPointerQueryCensus::default()
                    }
                );
            } else {
                assert_eq!(
                    census,
                    StaticFunctionPointerQueryCensus {
                        exact_use_operands_visited: 1,
                        ..StaticFunctionPointerQueryCensus::default()
                    }
                );
            }
        }
        assert_eq!(
            analysis.cache_state(),
            StaticFunctionPointerCacheState {
                use_site_index_built: true,
                definition_index_built: false,
                provenance_index_built: false,
                dominator_tree_built: false,
            }
        );
    }

    #[test]
    fn typed_resolution_requires_the_exact_instruction_to_consume_the_value() {
        // Before exact operand authentication, the unrelated Return coordinate
        // could make this later FnDef appear to precede a fabricated use.
        let function = function(vec![indirect_call(0), fn_def(0, 7), return_void()]);
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(0), BlockId::new(0), 2),
            None
        );
        assert_eq!(
            analysis.cache_state(),
            StaticFunctionPointerCacheState {
                use_site_index_built: true,
                definition_index_built: false,
                provenance_index_built: false,
                dominator_tree_built: false,
            }
        );
    }

    #[test]
    fn typed_resolution_rejects_duplicate_value_and_block_ids() {
        let mut duplicate_values = vec![fn_def(0, 1), fn_def(0, 2)];
        for value in 100..112 {
            duplicate_values.push(InstrNode::new(Inst::NullPtr).with_result(ValueId::new(value)));
        }
        let use_instruction = duplicate_values.len();
        duplicate_values.push(indirect_call(0));
        duplicate_values.push(return_void());
        let duplicate_values = function(duplicate_values);
        let analysis = StaticFunctionPointerAnalysis::new(&duplicate_values);
        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(0), BlockId::new(0), use_instruction,),
            None
        );
        assert!(analysis.use_sites.get().is_some());
        assert!(analysis.definitions.get().is_some());
        assert!(analysis.provenances.get().is_none());
        assert!(analysis.dominators.get().is_none());

        let mut duplicate_blocks = Function::new(
            FuncId::new(0),
            "duplicate_blocks",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        duplicate_blocks.blocks = vec![
            Block {
                id: BlockId::new(0),
                params: Vec::new(),
                body: vec![indirect_call(0), return_void()],
            },
            Block {
                id: BlockId::new(0),
                params: Vec::new(),
                body: vec![indirect_call(0), return_void()],
            },
        ];
        let analysis = StaticFunctionPointerAnalysis::new(&duplicate_blocks);
        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(0), BlockId::new(0), 0),
            None
        );
        assert_eq!(
            analysis.cache_state(),
            StaticFunctionPointerCacheState {
                use_site_index_built: true,
                definition_index_built: false,
                provenance_index_built: false,
                dominator_tree_built: false,
            }
        );
    }

    #[test]
    fn shared_deep_chain_is_summarized_once_and_stored_sparsely() {
        const ORDINARY_VALUES: u32 = 512;
        const CHAIN_DEFINITIONS: u32 = 513;
        const CALL_COUNT: u32 = 256;

        let mut nodes = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(0)),
        ];
        for value in 1..ORDINARY_VALUES {
            nodes.push(
                InstrNode::new(Inst::Copy {
                    ty: Ty::I32,
                    operand: ValueId::new(value - 1),
                })
                .with_result(ValueId::new(value)),
            );
        }
        let origin = ORDINARY_VALUES;
        nodes.push(fn_def(origin, 7));
        for offset in 1..CHAIN_DEFINITIONS {
            nodes.push(copy(origin + offset, origin + offset - 1));
        }
        let callee = origin + CHAIN_DEFINITIONS - 1;
        let first_call = nodes.len();
        for _ in 0..CALL_COUNT {
            nodes.push(indirect_call(callee));
        }
        nodes.push(return_void());

        let function = function(nodes);
        let analysis = StaticFunctionPointerAnalysis::new(&function);
        let mut provenance_visits = 0usize;
        let mut provenance_links = 0usize;
        let mut provenance_lookups = 0usize;
        let mut exact_use_checks = 0usize;
        let mut exact_use_operands = 0usize;
        let mut prefilter_visits = 0usize;
        for call in 0..CALL_COUNT as usize {
            let (resolution, census) = analysis.resolve_typed_at_with_census(
                ValueId::new(callee),
                BlockId::new(0),
                first_call + call,
            );
            let resolution = resolution.expect("the shared chain remains static");
            assert_eq!(resolution.function(), FuncId::new(7));
            assert_eq!(resolution.chain_definitions(), CHAIN_DEFINITIONS as usize);
            if call == 0 {
                let all_definitions = ORDINARY_VALUES + CHAIN_DEFINITIONS;
                assert_eq!(census.definition_values_indexed, all_definitions as usize);
                assert_eq!(
                    census.provenance_definitions_visited,
                    (all_definitions + CHAIN_DEFINITIONS) as usize
                );
                assert_eq!(census.provenance_entries_stored, CHAIN_DEFINITIONS as usize);
                assert_eq!(
                    census.provenance_links_validated,
                    CHAIN_DEFINITIONS as usize - 1
                );
                assert_eq!(census.dominator_blocks_indexed, 1);
                assert_eq!(
                    census.dominator_instructions_indexed,
                    (ORDINARY_VALUES + CHAIN_DEFINITIONS + CALL_COUNT + 1) as usize
                );
                assert_eq!(census.dominator_edges_indexed, 0);
            } else {
                assert_eq!(census.provenance_definitions_visited, 0);
                assert_eq!(census.provenance_entries_stored, 0);
                assert_eq!(census.provenance_links_validated, 0);
                assert_eq!(census.prefilter_instructions_visited, 0);
            }
            provenance_visits += census.provenance_definitions_visited;
            provenance_links += census.provenance_links_validated;
            provenance_lookups += census.provenance_summary_lookups;
            exact_use_checks += census.exact_use_dominance_checks;
            exact_use_operands += census.exact_use_operands_visited;
            prefilter_visits += census.prefilter_instructions_visited;
        }

        assert_eq!(
            provenance_visits,
            (ORDINARY_VALUES + CHAIN_DEFINITIONS * 2) as usize
        );
        assert_eq!(provenance_links, CHAIN_DEFINITIONS as usize - 1);
        assert_eq!(provenance_lookups, CALL_COUNT as usize);
        assert_eq!(exact_use_checks, CALL_COUNT as usize);
        assert_eq!(exact_use_operands, CALL_COUNT as usize);
        assert!(prefilter_visits <= LOCAL_PREFILTER_INSTRUCTION_LIMIT);
        assert_eq!(
            analysis.cache_state(),
            StaticFunctionPointerCacheState {
                use_site_index_built: true,
                definition_index_built: true,
                provenance_index_built: true,
                dominator_tree_built: true,
            }
        );
    }

    #[test]
    fn malformed_pointer_copy_does_not_retain_ordinary_copy_chain() {
        const ORDINARY_COPIES: u32 = 511;

        let mut nodes = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(0)),
        ];
        for value in 1..=ORDINARY_COPIES {
            nodes.push(
                InstrNode::new(Inst::Copy {
                    ty: Ty::I32,
                    operand: ValueId::new(value - 1),
                })
                .with_result(ValueId::new(value)),
            );
        }
        let malformed_pointer = ORDINARY_COPIES + 1;
        nodes.push(
            InstrNode::new(Inst::Copy {
                ty: Ty::Ptr,
                operand: ValueId::new(ORDINARY_COPIES),
            })
            .with_result(ValueId::new(malformed_pointer)),
        );
        // Keep the candidate outside the bounded local prefilter window so
        // this exercises the sparse whole-function provenance closure.
        for value in malformed_pointer + 1..=malformed_pointer + 10 {
            nodes.push(InstrNode::new(Inst::NullPtr).with_result(ValueId::new(value)));
        }
        let use_instruction = nodes.len();
        nodes.push(indirect_call(malformed_pointer));
        nodes.push(return_void());

        let function = function(nodes);
        let analysis = StaticFunctionPointerAnalysis::new(&function);
        let (resolution, census) = analysis.resolve_typed_at_with_census(
            ValueId::new(malformed_pointer),
            BlockId::new(0),
            use_instruction,
        );

        assert_eq!(resolution, None);
        assert_eq!(census.provenance_entries_stored, 1);
        assert_eq!(census.provenance_links_validated, 1);
        assert_eq!(census.provenance_summary_lookups, 1);
        assert_eq!(
            analysis.provenances.get().map(|index| index.entries.len()),
            Some(1)
        );
    }

    #[test]
    fn typed_cyclic_provenance_is_memoized_as_rejected() {
        let function = function(vec![
            copy(0, 1),
            copy(1, 0),
            indirect_call(0),
            return_void(),
        ]);
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        let (resolution, census) =
            analysis.resolve_typed_at_with_census(ValueId::new(0), BlockId::new(0), 2);
        assert_eq!(resolution, None);
        assert_eq!(census.provenance_entries_stored, 2);
        assert_eq!(census.provenance_links_validated, 2);
        assert_eq!(census.provenance_summary_lookups, 1);
        assert_eq!(census.exact_use_dominance_checks, 0);
        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(0), BlockId::new(0), 2),
            None
        );
    }

    #[test]
    fn many_local_dynamic_calls_use_bounded_cache_free_prefilter() {
        const CALL_COUNT: u32 = 512;

        let mut nodes = Vec::with_capacity(CALL_COUNT as usize * 2 + 1);
        let mut uses = Vec::with_capacity(CALL_COUNT as usize);
        for value in 0..CALL_COUNT {
            nodes.push(InstrNode::new(Inst::NullPtr).with_result(ValueId::new(value)));
            let use_instruction_index = nodes.len();
            nodes.push(indirect_call(value));
            uses.push((ValueId::new(value), use_instruction_index));
        }
        nodes.push(return_void());
        let function = function(nodes);
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        for (value, use_instruction_index) in uses {
            let window = local_prefilter_instruction_window(
                function.blocks[0].body.len(),
                use_instruction_index,
            );
            assert!(window.len() <= LOCAL_PREFILTER_INSTRUCTION_LIMIT);
            assert_eq!(
                analysis.resolve_typed_at(value, BlockId::new(0), use_instruction_index),
                None
            );
        }
        assert!(analysis.definitions.get().is_none());
        assert!(analysis.provenances.get().is_none());
        assert!(analysis.dominators.get().is_none());
    }

    #[test]
    fn typed_resolution_rejects_same_block_forward_definition() {
        let function = function(vec![indirect_call(0), fn_def(0, 7), return_void()]);
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(0), BlockId::new(0), 0),
            None
        );
        assert!(analysis.definitions.get().is_none());
        assert!(analysis.dominators.get().is_none());
    }

    #[test]
    fn typed_resolution_accepts_dominator_and_rejects_sibling_definition() {
        let mut dominating = Function::new(
            FuncId::new(0),
            "dominating",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        let mut entry = Block::new(BlockId::new(0));
        entry.params.push((ValueId::new(9), Ty::Bool));
        entry.body.push(fn_def(0, 7));
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: ValueId::new(9),
            then_target: BlockId::new(1),
            then_args: Vec::new(),
            else_target: BlockId::new(2),
            else_args: Vec::new(),
        }));
        let mut then_block = Block::new(BlockId::new(1));
        then_block.body.push(indirect_call(0));
        then_block.body.push(return_void());
        let mut else_block = Block::new(BlockId::new(2));
        else_block.body.push(return_void());
        dominating.blocks = vec![entry, then_block, else_block];

        let analysis = StaticFunctionPointerAnalysis::new(&dominating);
        assert_eq!(
            analysis
                .resolve_typed_at(ValueId::new(0), BlockId::new(1), 0)
                .map(|resolution| resolution.function()),
            Some(FuncId::new(7))
        );

        let mut sibling = dominating.clone();
        let definition = sibling.blocks[0].body.remove(0);
        sibling.blocks[1].body.insert(0, definition);
        sibling.blocks[2].body.insert(0, indirect_call(0));
        let analysis = StaticFunctionPointerAnalysis::new(&sibling);
        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(0), BlockId::new(2), 0),
            None
        );
    }

    #[test]
    fn typed_resolution_rejects_copy_type_laundering_and_invalid_cfg() {
        let mut laundering = function(vec![
            fn_def(0, 7),
            InstrNode::new(Inst::Copy {
                ty: Ty::Ptr,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            indirect_call(1),
            return_void(),
        ]);
        let analysis = StaticFunctionPointerAnalysis::new(&laundering);
        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(1), BlockId::new(0), 2),
            None
        );

        laundering.blocks[0].body.pop();
        let analysis = StaticFunctionPointerAnalysis::new(&laundering);
        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(1), BlockId::new(0), 2),
            None
        );
    }

    #[test]
    fn typed_resolution_rejects_signature_laundering_through_raw_pointer() {
        let function = function(vec![
            fn_def(0, 7),
            reify_to_pointer(1, 0),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Func(FuncTyId::new(1)),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(FuncTyId::new(1)),
                dst_ty: Ty::Ptr,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            indirect_call(3),
            return_void(),
        ]);
        let analysis = StaticFunctionPointerAnalysis::new(&function);

        assert_eq!(
            analysis.resolve_typed_at(ValueId::new(3), BlockId::new(0), 4),
            None
        );
    }

    #[test]
    fn dominator_tree_fails_closed_on_duplicate_blocks_and_unknown_edges() {
        let mut duplicate = function(vec![return_void()]);
        duplicate.blocks.push(Block::new(BlockId::new(0)));
        let tree = DominatorTree::new(&duplicate);
        assert!(!tree.is_well_formed());
        assert_eq!(tree.immediate_dominator(BlockId::new(0)), None);

        let mut unknown_edge = Function::new(
            FuncId::new(0),
            "unknown_edge",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(InstrNode::new(Inst::Br {
            target: BlockId::new(99),
            args: Vec::new(),
        }));
        unknown_edge.blocks.push(entry);
        let tree = DominatorTree::new(&unknown_edge);
        assert!(!tree.is_well_formed());
        assert_eq!(tree.immediate_dominator(BlockId::new(0)), None);
        assert_eq!(tree.immediate_dominator(BlockId::new(99)), None);
    }

    #[test]
    fn immediate_dominators_follow_sparse_diamond_and_ignore_unreachable_predecessor() {
        let mut function =
            Function::new(FuncId::new(0), "diamond", FuncTyId::new(0), BlockId::new(7));
        let mut entry = Block::new(BlockId::new(7));
        entry.params.push((ValueId::new(0), Ty::Bool));
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: ValueId::new(0),
            then_target: BlockId::new(22),
            then_args: vec![],
            else_target: BlockId::new(30),
            else_args: vec![],
        }));
        let edge = |source, target| {
            let mut block = Block::new(BlockId::new(source));
            block.body.push(InstrNode::new(Inst::Br {
                target: BlockId::new(target),
                args: vec![],
            }));
            block
        };
        let mut tail = Block::new(BlockId::new(55));
        tail.body.push(return_void());
        function.blocks = vec![
            edge(999, 40),
            tail,
            edge(30, 40),
            entry,
            edge(40, 55),
            edge(22, 40),
        ];
        let tree = DominatorTree::new(&function);
        assert!(tree.is_well_formed());
        for (block, parent) in [(22, 7), (30, 7), (40, 7), (55, 40)] {
            assert_eq!(
                tree.immediate_dominator(BlockId::new(block)),
                Some(BlockId::new(parent))
            );
        }
        for block in [7, 999, u32::MAX] {
            assert_eq!(tree.immediate_dominator(BlockId::new(block)), None);
        }
        assert_eq!(tree.immediate_dominator.len(), tree.reachable.len() - 1);
    }

    #[test]
    fn immediate_dominators_handle_loop_backedges_and_irreducible_cycles() {
        for edges in [
            vec![vec![1], vec![2], vec![1]],
            vec![vec![1], vec![0, 2], vec![1]],
            vec![vec![1, 2], vec![2], vec![1]],
        ] {
            let function = oracle_graph(&edges);
            let tree = DominatorTree::new(&function);
            assert!(tree.is_well_formed());
            let entry = function.blocks[0].id;
            let header = function.blocks[1].id;
            let body = function.blocks[2].id;
            assert_eq!(tree.immediate_dominator(entry), None);
            assert_eq!(tree.immediate_dominator(header), Some(entry));
            let body_parent = if edges[0].len() == 1 { header } else { entry };
            assert_eq!(tree.immediate_dominator(body), Some(body_parent));
        }
    }

    fn oracle_graph(edges: &[Vec<usize>]) -> Function {
        // Deliberately sparse, including the largest real ID: no synthetic
        // edge block is allocated or assumed available by this analysis.
        let ids = [
            BlockId::new(u32::MAX),
            BlockId::new(17),
            BlockId::new(4_000_000_000),
        ];
        let mut function = Function::new(FuncId::new(0), "edge_oracle", FuncTyId::new(0), ids[0]);
        for (source, targets) in edges.iter().enumerate() {
            let mut block = Block::new(ids[source]);
            let inst = if targets.is_empty() {
                Inst::Return { values: vec![] }
            } else {
                Inst::Switch {
                    value: ValueId::new(0),
                    default: ids[*targets.last().unwrap()],
                    default_args: vec![],
                    exhaustive_enum_unreachable: false,
                    cases: targets
                        .iter()
                        .enumerate()
                        .take(targets.len() - 1)
                        .map(|(index, &target)| crate::inst::SwitchCase {
                            value: Constant::Int(index as i128),
                            target: ids[target],
                            args: vec![],
                        })
                        .collect(),
                }
            };
            block.body.push(InstrNode::new(inst));
            function.blocks.push(block);
        }
        function
    }

    fn oracle_reachable(edges: &[Vec<usize>], removed: Option<(usize, usize)>) -> [bool; 3] {
        let mut reachable = [true, false, false];
        let mut pending = vec![0];
        while let Some(source) = pending.pop() {
            for (index, &target) in edges[source].iter().enumerate() {
                if removed == Some((source, index)) || reachable[target] {
                    continue;
                }
                reachable[target] = true;
                pending.push(target);
            }
        }
        reachable
    }

    fn compare_edge_oracle(edges: &[Vec<usize>]) {
        let function = oracle_graph(edges);
        let dominance = DominatorTree::new(&function);
        assert!(dominance.is_well_formed());
        let reachable = oracle_reachable(edges, None);
        for (source, targets) in edges.iter().enumerate() {
            for index in 0..targets.len() {
                let without = oracle_reachable(edges, Some((source, index)));
                for target in 0..3 {
                    assert_eq!(
                        dominance.edge_dominates(
                            function.blocks[source].id,
                            index,
                            function.blocks[target].id
                        ),
                        reachable[target] && !without[target],
                        "edges={edges:?}, removed=({source},{index}), queried={target}",
                    );
                }
            }
            assert!(!dominance.edge_dominates(
                function.blocks[source].id,
                targets.len(),
                function.entry
            ));
        }
    }

    #[test]
    fn edge_dominance_matches_independent_edge_removal_for_all_three_node_graphs() {
        // All 512 directed graphs include irreducible cycles, self edges,
        // unreachable predecessors and incoming edges to the real entry.
        for mask in 0..(1u32 << 9) {
            let mut edges = vec![vec![]; 3];
            for (source, targets) in edges.iter_mut().enumerate() {
                for target in 0..3 {
                    if mask & (1 << (source * 3 + target)) != 0 {
                        targets.push(target);
                    }
                }
            }
            compare_edge_oracle(&edges);
            // Duplicate each possible existing edge in turn; identical source
            // and target must not collapse normal/unwind or then/else paths.
            for source in 0..3 {
                for index in 0..edges[source].len() {
                    let mut parallel = edges.clone();
                    parallel[source].push(edges[source][index]);
                    compare_edge_oracle(&parallel);
                }
            }
        }
    }

    #[test]
    fn invoke_availability_distinguishes_instruction_and_normal_edge_endpoints() {
        let mut function = oracle_graph(&[vec![1, 2], vec![1], vec![]]);
        let entry = function.entry;
        let normal = function.blocks[1].id;
        let unwind = function.blocks[2].id;
        function.blocks[0].body[0] = InstrNode::new(Inst::Invoke {
            callee: FuncId::new(1),
            args: vec![],
            normal_dest: normal,
            normal_args: vec![],
            unwind_dest: unwind,
        })
        .with_result(ValueId::new(0));
        let d = DominatorTree::new(&function);
        let result = SsaDefinitionSite {
            block: entry,
            instruction: Some(0),
        };
        assert!(!d.definition_available_at(
            result,
            SsaUseSite::BeforeInstruction {
                block: entry,
                instruction: 0
            }
        ));
        assert!(d.definition_available_at(result, SsaUseSite::InvokeNormalEdge { block: entry }));
        assert!(d.definition_available_at(
            result,
            SsaUseSite::BeforeInstruction {
                block: normal,
                instruction: 0
            }
        ));
        assert!(!d.definition_available_at(
            result,
            SsaUseSite::BeforeInstruction {
                block: unwind,
                instruction: 0
            }
        ));
        assert!(!d.definition_available_at(
            result,
            SsaUseSite::BeforeInstruction {
                block: normal,
                instruction: 1
            }
        ));
        assert!(!d.definition_available_at(result, SsaUseSite::InvokeNormalEdge { block: normal }));
        let invalid_definition = SsaDefinitionSite {
            block: entry,
            instruction: Some(1),
        };
        assert!(!d.definition_available_at(
            invalid_definition,
            SsaUseSite::InvokeNormalEdge { block: entry }
        ));
        // An alternate entry to the normal destination destroys result
        // availability there, while the exact successful return edge remains
        // a valid place to pass the newly produced result as a block argument.
        function.blocks[2].body[0] = InstrNode::new(Inst::Br {
            target: normal,
            args: vec![],
        });
        let d = DominatorTree::new(&function);
        assert!(!d.definition_available_at(
            result,
            SsaUseSite::BeforeInstruction {
                block: normal,
                instruction: 0
            }
        ));
        assert!(d.definition_available_at(result, SsaUseSite::InvokeNormalEdge { block: entry }));
        // Parallel normal/unwind edges to the same destination are distinct.
        if let Inst::Invoke { unwind_dest, .. } = &mut function.blocks[0].body[0].inst {
            *unwind_dest = normal;
        }
        assert!(!DominatorTree::new(&function).edge_dominates(entry, 0, normal));
    }

    // --- indirect-call pools ------------------------------------------------

    fn shape(abi: Option<u32>, params: &[ArgClass]) -> FnShape {
        FnShape {
            abi,
            variadic: Some(false),
            params: Some(params.to_vec()),
        }
    }

    #[test]
    fn fn_shapes_match_componentwise_and_unstated_components_match_everything() {
        let int = shape(Some(0), &[ArgClass::Int(32)]);
        assert!(int.matches(&int));
        assert!(!int.matches(&shape(Some(0), &[ArgClass::Float(32)])));
        assert!(
            !int.matches(&shape(Some(3), &[ArgClass::Int(32)])),
            "ABI differs"
        );
        assert!(!int.matches(&shape(Some(0), &[])), "arity differs");
        assert!(
            int.matches(&shape(None, &[ArgClass::Int(32)])),
            "unstated ABI"
        );
        assert!(int.matches(&shape(Some(0), &[ArgClass::Unclassified])));
        assert!(int.matches(&FnShape::unclassified()));
        assert!(FnShape::unclassified().matches(&shape(Some(5), &[ArgClass::Exact(1)])));
        let variadic = FnShape {
            variadic: Some(true),
            ..int.clone()
        };
        assert!(!int.matches(&variadic));
    }

    /// A trust-ir shape states no ABI class: the producer's conventions on
    /// bodies and on fn-pointer calls disagree, so a stated one would split a
    /// pool. Missing signatures are unclassified.
    #[test]
    fn trust_ir_shapes_state_no_convention() {
        let mut module = Module::new("shapes");
        module.func_types.push(crate::FuncTy {
            abi: None,
            params: vec![Ty::U32],
            returns: Vec::new(),
            is_vararg: true,
        });
        let shape = fn_pool_shape(&module, FuncTyId::new(0));
        assert_eq!(shape.abi, None);
        assert_eq!(shape.variadic, Some(true));
        assert_eq!(shape.params, Some(vec![ArgClass::Int(32)]));
        assert_eq!(
            fn_pool_shape(&module, FuncTyId::new(9)),
            FnShape::unclassified()
        );
    }

    /// Classes never separate types Rust lets one call through the other:
    /// all thin pointers share one, integers ignore sign, `char` is `u32`,
    /// `bool` is `u8`, a transparent wrapper is its payload, and anything the
    /// spelling cannot settle is unclassified.
    #[test]
    fn argument_classes_never_split_abi_compatible_types() {
        use crate::{FieldDef, StructDef, TargetInfo};
        let mut module = Module::new("classes");
        let field = |ty: Ty| FieldDef {
            name: "f".into(),
            ty,
            offset: None,
        };
        let structure = |id: u32, repr: StructRepr, fields: Vec<FieldDef>| StructDef {
            id: crate::StructId::new(id),
            name: format!("s{id}"),
            fields,
            size: None,
            align: None,
            repr,
            origin: None,
        };
        module.structs = vec![
            // repr(transparent) over u64 with a zero-sized marker.
            structure(
                1,
                StructRepr::Transparent,
                vec![field(Ty::U64), field(Ty::Unit)],
            ),
            // Two fields the spelling cannot prove zero-sized.
            structure(
                2,
                StructRepr::Transparent,
                vec![field(Ty::U64), field(Ty::U8)],
            ),
            structure(3, StructRepr::Rust, vec![field(Ty::U64)]),
        ];
        module.types = vec![Ty::U32];
        let class = |module: &Module, ty: Ty| arg_class(module, &ty, 0);
        for thin in [
            Ty::Ptr,
            Ty::Ref(Box::new(Ty::U8)),
            Ty::RefMut(Box::new(Ty::U8)),
            Ty::PtrConst(Box::new(Ty::U8)),
            Ty::PtrMut(Box::new(Ty::U8)),
            Ty::Rc(Box::new(Ty::U8)),
            Ty::Func(FuncTyId::new(0)),
        ] {
            assert_eq!(class(&module, thin), ArgClass::ThinPointer);
        }
        assert_eq!(class(&module, Ty::I32), class(&module, Ty::U32));
        assert_eq!(class(&module, Ty::Char), ArgClass::Int(32));
        assert_eq!(class(&module, Ty::Bool), ArgClass::Int(8));
        assert_eq!(
            class(
                &module,
                Ty::Refine(crate::TyId::new(0), crate::PredId::new(0))
            ),
            ArgClass::Int(32)
        );
        assert_eq!(
            class(&module, Ty::Struct(crate::StructId::new(1))),
            ArgClass::Int(64)
        );
        assert_eq!(
            class(&module, Ty::Struct(crate::StructId::new(2))),
            ArgClass::Unclassified
        );
        assert!(matches!(
            class(&module, Ty::Struct(crate::StructId::new(3))),
            ArgClass::Exact(_)
        ));
        assert_eq!(
            class(&module, Ty::Enum(crate::EnumId::new(0))),
            ArgClass::Unclassified
        );
        assert_eq!(
            class(&module, Ty::Struct(crate::StructId::new(9))),
            ArgClass::Unclassified,
            "a missing definition"
        );
        assert_eq!(
            class(&module, Ty::Usize),
            ArgClass::Unclassified,
            "no target"
        );
        module.target_info = Some(TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        assert_eq!(class(&module, Ty::Usize), class(&module, Ty::U64));
        assert_ne!(class(&module, Ty::F64), class(&module, Ty::U64));
        assert_eq!(
            class(&module, Ty::FatPtr(crate::FatPtrKind::Str)),
            class(
                &module,
                Ty::FatPtr(crate::FatPtrKind::Slice(crate::TyId::new(0)))
            )
        );

        // Any two zero-sized, 1-aligned types are ABI-compatible, so no
        // zero-sized type, and no type not proved non-zero-sized, is `Exact`.
        module.structs.push(StructDef {
            size: Some(0),
            ..structure(4, StructRepr::Rust, Vec::new())
        });
        module
            .structs
            .push(structure(5, StructRepr::Rust, vec![field(Ty::Unit)]));
        module.structs.push(structure(
            6,
            StructRepr::Rust,
            vec![field(Ty::Enum(crate::EnumId::new(0)))],
        ));
        for zero_sized in [
            Ty::Struct(crate::StructId::new(4)),
            Ty::Struct(crate::StructId::new(5)),
            Ty::Array(crate::TyId::new(0), 0),
            Ty::Tuple(Vec::new()),
            Ty::Tuple(vec![Ty::Unit, Ty::Array(crate::TyId::new(0), 0)]),
            Ty::Struct(crate::StructId::new(6)),
            Ty::Closure(crate::ClosureTyId::new(0)),
        ] {
            assert_eq!(
                class(&module, zero_sized.clone()),
                ArgClass::Unclassified,
                "{zero_sized:?}"
            );
        }
        assert!(matches!(
            class(&module, Ty::Array(crate::TyId::new(0), 2)),
            ArgClass::Exact(_)
        ));
        assert!(matches!(
            class(&module, Ty::Tuple(vec![Ty::Unit, Ty::U8])),
            ArgClass::Exact(_)
        ));
    }

    #[test]
    fn launder_is_a_reinterpreting_cast_of_a_callable_carrying_type() {
        let mut module = Module::new("launder");
        module.func_types.push(crate::FuncTy {
            abi: None,
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.func_types.push(crate::FuncTy {
            abi: None,
            params: vec![Ty::U32],
            returns: Vec::new(),
            is_vararg: false,
        });
        let nominal = module.nominal_type_reachability();
        let func = Ty::Func(FuncTyId::new(0));
        let other = Ty::Func(FuncTyId::new(1));
        let object = Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 3 });
        assert!(cast_launders(&nominal, CastOp::Transmute, &func, &other));
        assert!(cast_launders(&nominal, CastOp::PtrToInt, &func, &Ty::Usize));
        assert!(cast_launders(&nominal, CastOp::PtrToPtr, &object, &Ty::Ptr));
        assert!(
            !cast_launders(&nominal, CastOp::Transmute, &func, &func),
            "same type"
        );
        assert!(!cast_launders(
            &nominal,
            CastOp::ReifyFnPointer,
            &func,
            &Ty::Ptr
        ));
        assert!(!cast_launders(
            &nominal,
            CastOp::PtrToInt,
            &Ty::Ptr,
            &Ty::Usize
        ));
        assert!(!cast_launders(&nominal, CastOp::ZExt, &Ty::U8, &Ty::U32));
    }

    /// The summaries close over cycles: every node of a strongly connected
    /// component invokes what any of them, or anything after them, invokes,
    /// and one opaque node anywhere downstream makes it every key.
    #[test]
    fn rule_h_summaries_close_over_cycles_and_opaque_code() {
        // 0 -> 1 <-> 2 -> 3;  4 -> 5 (opaque);  6 alone.
        let successors = vec![
            vec![1],
            vec![2],
            vec![1, 3],
            vec![],
            vec![5],
            vec![],
            vec![],
        ];
        let own = vec![vec![], vec![0], vec![], vec![1], vec![], vec![], vec![2]];
        let everything = vec![false, false, false, false, false, true, false];
        let summaries = InvokedKeySummaries::new(&successors, &own, &everything);
        let some = |keys: &[usize]| InvokedKeys::Some(keys.iter().copied().collect());
        assert_eq!(summaries.of(0), &some(&[0, 1]));
        assert_eq!(summaries.of(1), &some(&[0, 1]));
        assert_eq!(summaries.of(2), &some(&[0, 1]));
        assert_eq!(summaries.of(3), &some(&[1]));
        assert_eq!(summaries.of(4), &InvokedKeys::Every);
        assert_eq!(summaries.of(6), &some(&[2]));
    }
}
