// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only inspection inside an owned, replayed logical dependency cone.
//! Candidate expressions are untrusted kernel inputs, never context receipts.
//! Runtime substitutions, native semantics and application policy are separate.

use std::collections::{BTreeSet, HashSet};
use std::sync::Arc;

use clean_kernel::{ConstantInfo, ConstructorVal, Expr, InductiveVal, Level, Name, TypeChecker};
use clean_olean::{ImportedConeGate, ImportedConeVerdict};

use super::{ExternalLeanError, ExternalLeanProgram};
mod input;

/// A failed context inspection grants no partial qualification.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReplayContextError {
    /// A cone must be rooted in at least one captured source declaration.
    #[error("replayed context requires an owned source root")]
    EmptyRoots,
    /// A name is not a dependency of the selected logical roots.
    #[error("`{name}` is outside this replayed dependency cone")]
    OutsideCone { name: Name },
    /// A declaration handle belongs to another elaboration, even if its name matches.
    #[error("declaration belongs to another external Lean program")]
    ForeignOwner,
    /// An actual kernel constant record was unavailable.
    #[error("replayed dependency `{name}` has no constant record")]
    MissingConstant { name: Name },
    /// Limits may never mean unlimited.
    #[error("replayed inspection requires positive node, heartbeat and cache limits")]
    InvalidLimits,
    /// Only closed, explicitly instantiated expressions can be checked here.
    #[error("replayed inspection requires a closed expression with closed universe levels")]
    OpenExpression,
    /// Explicit universe arguments must match the actual declaration arity.
    #[error("replayed declaration requires {expected} universe arguments, received {actual}")]
    UniverseArity { expected: usize, actual: usize },
    /// The external Lean world does not admit Clean-only expression extensions.
    #[error("replayed inspection requires an ordinary Lean expression")]
    ExtendedExpression,
    /// Structural input/output work exceeded its explicit allowance.
    #[error("replayed inspection exceeded its expanded structural allowance")]
    NodeLimit,
    /// A bounded reduction must not publish an under-reduced answer.
    #[error("replayed inspection exhausted its kernel heartbeat allowance")]
    HeartbeatLimit,
    /// The existing full-check kernel refused a candidate.
    #[error("replayed inspection kernel check failed: {0}")]
    Kernel(#[source] Box<clean_kernel::TypeError>),
}

/// Finite per-operation limits; zero never disables a check. Structural units
/// include expression/expanded-level nodes, Name components, UTF-8 bytes,
/// big-natural limbs and metadata entries.
#[derive(Debug, Clone, Copy)]
pub struct ReplayContextLimits {
    nodes: usize,
    heartbeats: u32,
    cache_entries: usize,
}

impl ReplayContextLimits {
    /// Set structural, kernel-work and cache bounds for one complete operation.
    pub fn new(
        nodes: usize,
        heartbeats: u32,
        cache_entries: usize,
    ) -> Result<Self, ReplayContextError> {
        if nodes == 0 || heartbeats == 0 || cache_entries == 0 {
            return Err(ReplayContextError::InvalidLimits);
        }
        Ok(Self {
            nodes,
            heartbeats,
            cache_entries,
        })
    }
}

impl Default for ReplayContextLimits {
    fn default() -> Self {
        Self {
            nodes: 100_000,
            heartbeats: 1_000_000,
            cache_entries: 100_000,
        }
    }
}

/// An immutable borrowed logical context, minted only by source-owned replay.
/// Imported dependencies may be inspected, but gain no source-selection right.
pub struct ReplayedLeanContext<'program> {
    program: &'program ExternalLeanProgram,
    roots: BTreeSet<Name>,
    inspection_roots: BTreeSet<Name>,
    members: BTreeSet<Name>,
    member_index: HashSet<Name>,
    verdict: ImportedConeVerdict,
}

impl ExternalLeanProgram {
    /// Replay the union of these actual source-owned roots, retaining this
    /// program's private environment and custody. Names/hashes cannot supply
    /// an environment, expand the resulting cone or waive replay refusals.
    pub fn replay_context(
        &self,
        roots: &[Name],
    ) -> Result<ReplayedLeanContext<'_>, ExternalLeanError> {
        let roots: BTreeSet<_> = roots.iter().cloned().collect();
        if roots.is_empty() {
            return Err(ReplayContextError::EmptyRoots.into());
        }
        for root in &roots {
            if !self.module_names.contains(root) {
                return Err(ExternalLeanError::Input(format!(
                    "{root:?} was not declared by the captured source module"
                )));
            }
        }
        ReplayedLeanContext::replay(self, roots.clone(), roots)
    }
}

impl<'program> ReplayedLeanContext<'program> {
    pub(super) fn same_program(&self, program: &ExternalLeanProgram) -> bool {
        Arc::ptr_eq(&self.program.custody, &program.custody)
            && self.program.world() == program.world()
    }
    fn replay(
        program: &'program ExternalLeanProgram,
        roots: BTreeSet<Name>,
        inspection_roots: BTreeSet<Name>,
    ) -> Result<Self, ExternalLeanError> {
        let mut gate = ImportedConeGate::new(&program.base);
        let verdict = gate.check(&program.env, &inspection_roots);
        if !verdict.passed(false) {
            return Err(ExternalLeanError::Replay {
                root: roots
                    .iter()
                    .next()
                    .cloned()
                    .ok_or(ReplayContextError::EmptyRoots)?,
                reason: verdict.refusal_summary(false),
                verdict: Box::new(verdict),
            });
        }
        let mut members = BTreeSet::new();
        for root in &inspection_roots {
            members.extend(
                program
                    .env
                    .dependency_closure(root)
                    .map_err(|e| ExternalLeanError::Input(e.to_string()))?,
            );
        }
        let member_index = members.iter().cloned().collect();
        Ok(ReplayedLeanContext {
            program,
            roots,
            inspection_roots,
            members,
            member_index,
            verdict,
        })
    }

    /// Exact source roots of this logical replay.
    pub fn roots(&self) -> impl ExactSizeIterator<Item = &Name> {
        self.roots.iter()
    }

    /// Every explicitly replayed inspection root. Additional imported roots
    /// are observations, not claims that a source term logically references them.
    pub fn inspection_roots(&self) -> impl ExactSizeIterator<Item = &Name> {
        self.inspection_roots.iter()
    }

    /// Explicitly replay further records from this same captured environment.
    /// Metadata can carry declaration Names as data, which are not logical
    /// constant references. A name requests a fresh full replay; it grants no
    /// authority on its own and never grants imported native selection.
    /// The original context stays immutable and usable if this call refuses.
    pub fn with_replayed_declarations(&self, names: &[Name]) -> Result<Self, ExternalLeanError> {
        let mut inspection_roots = self.inspection_roots.clone();
        for name in names {
            if self.program.env.get_const(name).is_none() {
                return Err(ReplayContextError::MissingConstant { name: name.clone() }.into());
            }
            inspection_roots.insert(name.clone());
        }
        Self::replay(self.program, self.roots.clone(), inspection_roots)
    }

    /// Actual structural dependency identities, including imported families.
    pub fn dependency_names(&self) -> impl ExactSizeIterator<Item = &Name> {
        self.members.iter()
    }

    /// The complete replay outcome, including axiom and trust-marker disclosure.
    pub fn replay_verdict(&self) -> &ImportedConeVerdict {
        &self.verdict
    }

    /// Resolve only a member of this replayed cone, never an arbitrary same-name record.
    pub fn declaration(
        &self,
        name: &Name,
    ) -> Result<ReplayedContextDeclaration<'_, 'program>, ReplayContextError> {
        self.require_member(name)?;
        let info = self
            .program
            .env
            .get_const(name)
            .ok_or_else(|| ReplayContextError::MissingConstant { name: name.clone() })?;
        Ok(ReplayedContextDeclaration {
            context: self,
            info,
        })
    }

    /// Check this same-program declaration, at explicit closed universe levels,
    /// against a closed expected type using the existing full-check kernel.
    pub fn check_expected_type(
        &self,
        declaration: &ReplayedContextDeclaration<'_, '_>,
        levels: &[Level],
        expected: &Expr,
        limits: ReplayContextLimits,
    ) -> Result<(), ReplayContextError> {
        if !Arc::ptr_eq(&self.program.custody, &declaration.context.program.custody) {
            return Err(ReplayContextError::ForeignOwner);
        }
        let mut remaining = limits.nodes;
        let term = input::declaration_term(self, declaration.info, levels, &mut remaining)?;
        self.check_expression(expected, &mut remaining)?;
        let checker = self.checker(limits);
        drop(checker.infer_sort(expected).map_err(kernel_error)?);
        checker.check_type(&term, expected).map_err(kernel_error)?;
        finish(&checker)
    }

    /// Compare fully checked, closed candidates in this exact logical context.
    /// A resource abort is an error, never a negative equality result.
    pub fn definitionally_equal(
        &self,
        left: &Expr,
        right: &Expr,
        limits: ReplayContextLimits,
    ) -> Result<bool, ReplayContextError> {
        let mut remaining = limits.nodes;
        self.check_expression(left, &mut remaining)?;
        self.check_expression(right, &mut remaining)?;
        let checker = self.checker(limits);
        let left_type = checker.infer_type_full(left).map_err(kernel_error)?;
        let right_type = checker.infer_type_full(right).map_err(kernel_error)?;
        let equal = checker.is_def_eq(&left_type, &right_type) && checker.is_def_eq(left, right);
        finish(&checker)?;
        Ok(equal)
    }

    /// Weak-head reduce a fully checked closed candidate with finite work and
    /// output bounds. This is logical reduction, independent of runtime bindings.
    pub fn whnf_closed(
        &self,
        expression: &Expr,
        limits: ReplayContextLimits,
    ) -> Result<Expr, ReplayContextError> {
        let mut remaining = limits.nodes;
        self.check_expression(expression, &mut remaining)?;
        let checker = self.checker(limits);
        drop(checker.infer_type_full(expression).map_err(kernel_error)?);
        let result = checker.whnf(expression);
        finish(&checker)?;
        self.check_expression(&result, &mut remaining)?;
        Ok(result)
    }

    fn checker(&self, limits: ReplayContextLimits) -> TypeChecker<'_> {
        let mut checker = TypeChecker::new(&self.program.env);
        checker.set_heartbeat_limit(limits.heartbeats);
        checker.set_max_cache_entries(limits.cache_entries);
        checker
    }

    fn require_member(&self, name: &Name) -> Result<(), ReplayContextError> {
        if self.member_index.contains(name) {
            Ok(())
        } else {
            Err(ReplayContextError::OutsideCone { name: name.clone() })
        }
    }

    fn check_expression(
        &self,
        expression: &Expr,
        remaining: &mut usize,
    ) -> Result<(), ReplayContextError> {
        input::expression(self, expression, remaining)
    }
}

/// A borrowed record reachable through one actual replay context. The private
/// fields cannot be rebuilt from caller-supplied records, names or digests.
pub struct ReplayedContextDeclaration<'context, 'program> {
    context: &'context ReplayedLeanContext<'program>,
    info: &'program ConstantInfo,
}

impl ReplayedContextDeclaration<'_, '_> {
    /// The actual kernel record in the owned context.
    pub fn constant(&self) -> &ConstantInfo {
        self.info
    }
    /// Actual constructor metadata; never inferred by appending `mk` to a type name.
    pub fn constructor(&self) -> Option<&ConstructorVal> {
        self.context.program.env.get_constructor(&self.info.name)
    }
    /// Actual inductive-family metadata.
    pub fn inductive(&self) -> Option<&InductiveVal> {
        self.context.program.env.get_inductive(&self.info.name)
    }
    /// Imported dependencies remain distinguishable from source-owned declarations.
    pub fn is_source_owned(&self) -> bool {
        self.context.program.module_names.contains(&self.info.name)
    }
}

fn kernel_error(error: clean_kernel::TypeError) -> ReplayContextError {
    ReplayContextError::Kernel(Box::new(error))
}

fn finish(checker: &TypeChecker<'_>) -> Result<(), ReplayContextError> {
    // Observe latent resource/world errors from non-Result reduction paths too.
    drop(
        checker
            .infer_type_full(&Expr::sort(Level::zero()))
            .map_err(kernel_error)?,
    );
    if checker.heartbeat_spent() {
        return Err(ReplayContextError::HeartbeatLimit);
    }
    Ok(())
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod version_tests;

#[cfg(test)]
mod ordinary_tests;
