//! Bounded primary-artifact membership facts, never ownership or checking tokens.

use super::{ArtifactDepth, LoadModule};
use clean_kernel::{name::NameInner, Name};
use std::cmp::Ordering;

/// Where an identity occurs in the authoritative part, without owner promotion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArtifactDeclarationOrigin {
    /// An actual Lean-format constant record.
    LeanRecord,
    /// A declaration in the actual Clean payload.
    CleanPayload,
    /// The same identity occurs in both representations.
    Both,
}

impl ArtifactDeclarationOrigin {
    fn includes(self, other: Self) -> bool {
        self == Self::Both || self == other
    }
}

/// One ordinary, unverified artifact-membership observation.
#[derive(Debug, Clone)]
pub struct ArtifactDeclaration {
    name: Name,
    origin: ArtifactDeclarationOrigin,
}

impl ArtifactDeclaration {
    /// Exact structural identity, including private/unsafe/partial auxiliaries.
    pub fn name(&self) -> &Name {
        &self.name
    }
    /// Actual record/payload occurrence, not source or native-selection rights.
    pub fn origin(&self) -> ArtifactDeclarationOrigin {
        self.origin
    }
}

/// Why no complete inventory was produced. No prefix accompanies an error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum ArtifactInventoryError {
    /// Both bounds must be positive.
    #[error("artifact inventory requires positive declaration and work limits")]
    InvalidLimits,
    /// The compatibility array projection was not a strict successful read.
    #[error("artifact declaration/name arrays are unavailable or malformed")]
    MalformedArrays,
    /// Strict name-array and raw-record membership disagree.
    #[error("artifact name-array and raw-record inventory differ")]
    NameRecordMismatch,
    /// One representation declares an identity twice.
    #[error("artifact inventory has a duplicate declaration in one representation")]
    DuplicateDeclaration,
    /// Record/payload occurrence capacity was exceeded.
    #[error("artifact inventory declaration occurrence limit")]
    DeclarationLimit,
    /// Expanded Name traversal/comparison/movement work was exhausted.
    #[error("artifact inventory structural work limit")]
    StructuralLimit,
}

/// Positive finite retention bounds, independent of kernel/native authority.
#[derive(Debug, Clone, Copy)]
pub struct ArtifactInventoryLimits {
    declarations: usize,
    work: usize,
}

impl ArtifactInventoryLimits {
    /// Bound occurrence count and new structural traversal/collection work.
    pub fn new(declarations: usize, work: usize) -> Result<Self, ArtifactInventoryError> {
        if declarations == 0 || work == 0 {
            return Err(ArtifactInventoryError::InvalidLimits);
        }
        Ok(Self { declarations, work })
    }
}

impl Default for ArtifactInventoryLimits {
    fn default() -> Self {
        Self {
            declarations: 100_000,
            work: 64 * 1024 * 1024,
        }
    }
}

/// Complete unique membership of the authoritative part, as ordinary data.
/// This does not replace compatibility constNames or any ownership predicate.
#[derive(Debug, Clone)]
pub struct ArtifactInventory {
    declarations: Vec<ArtifactDeclaration>,
    occurrences: usize,
}

impl ArtifactInventory {
    /// Complete unique identities, ordered by a structural binary Name key.
    pub fn declarations(&self) -> &[ArtifactDeclaration] {
        &self.declarations
    }
    /// Raw plus payload occurrences, including both-origin duplicates.
    pub fn occurrences(&self) -> usize {
        self.occurrences
    }
    /// Directly traverse every expanded Name before a new bounded observation.
    /// Returns actual charged units; no serialization/hash cap substitutes.
    pub fn check_limits(
        &self,
        limits: ArtifactInventoryLimits,
    ) -> Result<usize, ArtifactInventoryError> {
        if self.occurrences > limits.declarations {
            return Err(ArtifactInventoryError::DeclarationLimit);
        }
        let mut budget = Budget(limits.work);
        for declaration in &self.declarations {
            walk_name(&declaration.name, &mut budget)?;
        }
        Ok(limits.work - budget.0)
    }
}

struct Budget(usize);
impl Budget {
    fn spend(&mut self, n: usize) -> Result<(), ArtifactInventoryError> {
        self.0 = self
            .0
            .checked_sub(n)
            .ok_or(ArtifactInventoryError::StructuralLimit)?;
        Ok(())
    }
}

fn walk_name(mut name: &Name, budget: &mut Budget) -> Result<(), ArtifactInventoryError> {
    loop {
        budget.spend(1)?;
        match name.inner() {
            NameInner::Anon => return Ok(()),
            NameInner::Str(parent, text) => {
                budget.spend(text.len())?;
                name = parent;
            }
            NameInner::Num(parent, _) => {
                budget.spend(8)?;
                name = parent;
            }
        }
    }
}

// Do not invoke recursive Name Ord, pretty-printing or an unmetered sort.
// The key retains every constructor boundary/byte; it is not Name.to_string.
fn key(mut name: &Name, budget: &mut Budget) -> Result<Vec<u8>, ArtifactInventoryError> {
    let mut parts = Vec::new();
    loop {
        budget.spend(1)?;
        match name.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, text) => {
                budget.spend(9)?;
                budget.spend(text.len())?;
                parts.push(name.inner());
                name = parent;
            }
            NameInner::Num(parent, _) => {
                budget.spend(9)?;
                parts.push(name.inner());
                name = parent;
            }
        }
    }
    budget.spend(parts.len())?;
    let mut result = vec![0];
    for part in parts.into_iter().rev() {
        match part {
            NameInner::Str(_, text) => {
                result.push(1);
                let len = u64::try_from(text.len())
                    .map_err(|_| ArtifactInventoryError::StructuralLimit)?;
                result.extend_from_slice(&len.to_be_bytes());
                result.extend_from_slice(text.as_bytes());
            }
            NameInner::Num(_, number) => {
                result.push(2);
                result.extend_from_slice(&number.to_be_bytes());
            }
            NameInner::Anon => {}
        }
    }
    Ok(result)
}

fn compare(a: &[u8], b: &[u8], budget: &mut Budget) -> Result<Ordering, ArtifactInventoryError> {
    for (a, b) in a.iter().zip(b) {
        budget.spend(1)?;
        let order = a.cmp(b);
        if order != Ordering::Equal {
            return Ok(order);
        }
    }
    budget.spend(1)?;
    Ok(a.len().cmp(&b.len()))
}

struct Entry {
    key: Vec<u8>,
    declaration: ArtifactDeclaration,
    header_seen: bool,
}

fn locate(
    entries: &[Entry],
    key: &[u8],
    budget: &mut Budget,
) -> Result<Result<usize, usize>, ArtifactInventoryError> {
    let (mut lo, mut hi) = (0, entries.len());
    while lo < hi {
        budget.spend(1)?;
        let mid = lo + (hi - lo) / 2;
        match compare(key, &entries[mid].key, budget)? {
            Ordering::Equal => return Ok(Ok(mid)),
            Ordering::Less => hi = mid,
            Ordering::Greater => lo = mid + 1,
        }
    }
    Ok(Err(lo))
}

/// One borrowed occurrence traversal shared with the compatibility placement check.
pub(super) fn occurrences(
    part: &LoadModule,
    depth: ArtifactDepth,
) -> Box<dyn Iterator<Item = (&Name, ArtifactDeclarationOrigin)> + '_> {
    let raw: Box<dyn Iterator<Item = &Name>> = match depth {
        ArtifactDepth::Names => Box::new(part.const_names.iter()),
        ArtifactDepth::Records => Box::new(part.constants.iter().map(|c| &c.kernel_name)),
    };
    let payload = part
        .clean_payload
        .iter()
        .flat_map(|p| p.declared_name_refs());
    Box::new(
        raw.map(|n| (n, ArtifactDeclarationOrigin::LeanRecord))
            .chain(payload.map(|n| (n, ArtifactDeclarationOrigin::CleanPayload))),
    )
}

pub(super) fn build(
    part: &LoadModule,
    limits: ArtifactInventoryLimits,
) -> Result<ArtifactInventory, ArtifactInventoryError> {
    if !part.inventory_arrays_valid {
        return Err(ArtifactInventoryError::MalformedArrays);
    }
    let mut budget = Budget(limits.work);
    budget.spend(1)?;
    let mut entries: Vec<Entry> = Vec::new();
    let mut count = 0usize;
    for (name, origin) in occurrences(part, ArtifactDepth::Records) {
        count = count
            .checked_add(1)
            .ok_or(ArtifactInventoryError::DeclarationLimit)?;
        if count > limits.declarations {
            return Err(ArtifactInventoryError::DeclarationLimit);
        }
        let key = key(name, &mut budget)?;
        match locate(&entries, &key, &mut budget)? {
            Ok(index) => {
                if entries[index].declaration.origin.includes(origin) {
                    return Err(ArtifactInventoryError::DuplicateDeclaration);
                }
                entries[index].declaration.origin = ArtifactDeclarationOrigin::Both;
            }
            Err(index) => {
                // Account for pointer movement/allocation before cloning a Name.
                budget.spend(entries.len())?;
                budget.spend(entries.len() - index)?;
                budget.spend(1)?;
                entries.insert(
                    index,
                    Entry {
                        key,
                        declaration: ArtifactDeclaration {
                            name: name.clone(),
                            origin,
                        },
                        header_seen: false,
                    },
                );
            }
        }
    }
    if part.const_names.len() != part.constants.len() {
        return Err(ArtifactInventoryError::NameRecordMismatch);
    }
    for name in &part.const_names {
        let key = key(name, &mut budget)?;
        let index = locate(&entries, &key, &mut budget)?
            .map_err(|_| ArtifactInventoryError::NameRecordMismatch)?;
        if entries[index].header_seen
            || !entries[index]
                .declaration
                .origin
                .includes(ArtifactDeclarationOrigin::LeanRecord)
        {
            return Err(ArtifactInventoryError::NameRecordMismatch);
        }
        entries[index].header_seen = true;
    }
    budget.spend(entries.len())?;
    Ok(ArtifactInventory {
        declarations: entries.into_iter().map(|e| e.declaration).collect(),
        occurrences: count,
    })
}

#[cfg(test)]
mod tests;
