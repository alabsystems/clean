// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Premise database: Premise, PremiseId, PremiseDatabase.

use super::{FeatureExtractor, FeatureSet};
use clean_kernel::{Expr, Name};
use std::collections::{HashMap, HashSet};

/// A known fact/premise in the database
#[derive(Clone, Debug)]
pub struct Premise {
    /// Unique identifier for this premise
    pub id: PremiseId,
    /// Name of the theorem/lemma
    pub name: Name,
    /// The statement (type of the theorem)
    pub statement: Expr,
    /// Extracted features for ML-based selection
    pub(crate) features: FeatureSet,
    /// Constants appearing in this premise (for MePo)
    pub constants: HashSet<Name>,
    /// Dependencies (other premises used in the proof)
    pub dependencies: Vec<PremiseId>,
}

/// Unique identifier for a premise
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PremiseId(pub u64);

impl Premise {
    /// Create a new premise
    pub fn new(id: PremiseId, name: Name, statement: Expr) -> Self {
        let extractor = FeatureExtractor::new();
        let features = extractor.extract(&statement);
        let constants = extractor.extract_constants(&statement);
        Self {
            id,
            name,
            statement,
            features,
            constants,
            dependencies: Vec::new(),
        }
    }

    /// Add a dependency
    pub fn add_dependency(&mut self, dep: PremiseId) {
        if !self.dependencies.contains(&dep) {
            self.dependencies.push(dep);
        }
    }
}

/// Database of known premises
#[derive(Default)]
pub struct PremiseDatabase {
    /// All premises indexed by ID
    premises: HashMap<PremiseId, Premise>,
    /// Premises indexed by name
    by_name: HashMap<Name, PremiseId>,
    /// Global constant frequencies (for MePo weighting)
    pub(super) const_freq: HashMap<Name, usize>,
    /// Total number of premises
    count: u64,
    /// Next available premise ID
    next_id: u64,
}

impl PremiseDatabase {
    /// Create a new empty premise database
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a premise to the database
    ///
    /// REQUIRES: `name` is a valid theorem/lemma name
    /// REQUIRES: `statement` is a well-formed type expression (the theorem statement)
    /// ENSURES: Returns a unique PremiseId for the new premise
    /// ENSURES: len() increases by 1
    /// ENSURES: get(returned_id) returns the added premise
    /// ENSURES: Updates const_freq for all constants in the statement
    pub fn add(&mut self, name: Name, statement: Expr) -> PremiseId {
        let id = PremiseId(self.next_id);
        self.next_id += 1;
        self.count += 1;

        let premise = Premise::new(id, name.clone(), statement);

        // Update constant frequencies
        for c in &premise.constants {
            *self.const_freq.entry(c.clone()).or_insert(0) += 1;
        }

        self.by_name.insert(name, id);
        self.premises.insert(id, premise);
        id
    }

    /// Get a premise by ID
    ///
    /// ENSURES: Returns Some(&premise) if id was previously returned by add()
    /// ENSURES: Returns None if id was never added to this database
    pub fn get(&self, id: PremiseId) -> Option<&Premise> {
        self.premises.get(&id)
    }

    /// Get a premise by name
    pub fn get_by_name(&self, name: &Name) -> Option<&Premise> {
        self.by_name.get(name).and_then(|id| self.premises.get(id))
    }

    /// Get the frequency of a constant
    pub fn const_frequency(&self, name: &Name) -> usize {
        self.const_freq.get(name).copied().unwrap_or(0)
    }

    /// Total number of premises
    pub fn len(&self) -> usize {
        self.count as usize
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Iterate over all premises
    pub fn iter(&self) -> impl Iterator<Item = &Premise> {
        self.premises.values()
    }

    /// Record a successful proof: update dependencies
    ///
    /// REQUIRES: `proved` should be a valid PremiseId from this database
    /// REQUIRES: `used_premises` should contain valid PremiseIds from this database
    /// ENSURES: If proved is valid, adds used_premises as dependencies (idempotent)
    /// ENSURES: If proved is invalid, no-op
    pub fn record_proof(&mut self, proved: PremiseId, used_premises: &[PremiseId]) {
        if let Some(premise) = self.premises.get_mut(&proved) {
            for &dep in used_premises {
                premise.add_dependency(dep);
            }
        }
    }
}
