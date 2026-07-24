// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core types for the CDCL SAT solver.
//!
//! Contains variable, literal, clause, and related type definitions
//! used throughout the solver.

/// A variable in the SAT problem (0-indexed internally)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub(crate) u32);

impl Var {
    /// Create a new variable with the given index
    #[inline]
    pub fn new(idx: u32) -> Self {
        Var(idx)
    }

    /// Get the raw variable index as u32
    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }

    /// Get the variable index
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A literal is a variable or its negation
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Lit(pub(crate) u32);

impl Lit {
    /// Create a positive literal
    #[inline]
    pub fn pos(var: Var) -> Self {
        Lit(var.0 << 1)
    }

    /// Create a negative literal
    #[inline]
    pub fn neg(var: Var) -> Self {
        Lit((var.0 << 1) | 1)
    }

    /// Create a literal from variable and sign (true = positive)
    #[inline]
    pub fn new(var: Var, sign: bool) -> Self {
        if sign {
            Self::pos(var)
        } else {
            Self::neg(var)
        }
    }

    /// Get the underlying variable
    #[inline]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    /// Check if this is a positive literal
    #[inline]
    pub fn is_pos(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Check if this is a negative literal
    #[inline]
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn is_neg(self) -> bool {
        (self.0 & 1) == 1
    }

    /// Get the negation of this literal
    #[inline]
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> Self {
        Lit(self.0 ^ 1)
    }

    /// Get the raw index (for array indexing, 2 entries per variable)
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Reference to a clause in the clause database
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ClauseRef(pub(crate) u32);

impl ClauseRef {
    pub const INVALID: ClauseRef = ClauseRef(u32::MAX);

    /// Construct a clause reference from a raw index
    #[inline]
    #[cfg_attr(
        not(feature = "fuzz"),
        expect(
            dead_code,
            reason = "raw clause references remain available for internal debug and future bridge helpers"
        )
    )]
    pub fn from_raw(raw: u32) -> Self {
        ClauseRef(raw)
    }

    /// Get the raw clause index as u32
    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }

    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    #[inline]
    pub fn is_valid(self) -> bool {
        self != Self::INVALID
    }
}

#[inline]
pub(super) fn usize_to_u32(value: usize, context: &str) -> u32 {
    u32::try_from(value).unwrap_or_else(|_| panic!("{context} exceeds u32::MAX: {value}"))
}

#[inline]
pub(super) fn clause_ref_at(len: usize) -> ClauseRef {
    ClauseRef(usize_to_u32(len, "clause index"))
}

/// A clause is a disjunction of literals
#[derive(Clone, Debug)]
pub struct Clause {
    /// The literals in this clause (first two are watched)
    pub(crate) lits: Vec<Lit>,
    /// Is this a learned clause?
    pub(crate) learned: bool,
    /// Activity score for learned clause deletion
    pub(crate) activity: f64,
    /// Literal Block Distance (LBD) for Glucose-style deletion
    pub(crate) lbd: u32,
    /// For learned clauses: original clause indices that contributed to this clause.
    /// Empty for original clauses (self-referential - use clause index instead).
    /// Used for unsat core extraction.
    pub(crate) origins: Vec<u32>,
    /// Whether this clause has been deleted by reduce_db.
    /// Deleted clauses remain in the Vec (to preserve indices) but are
    /// excluded from watch lists and propagation.
    pub(crate) deleted: bool,
}

impl Clause {
    /// Create a new clause
    pub fn new(lits: Vec<Lit>, learned: bool) -> Self {
        Self {
            lits,
            learned,
            activity: 0.0,
            lbd: 0,
            origins: Vec::new(),
            deleted: false,
        }
    }

    /// Create a new learned clause with origin tracking
    pub fn new_learned(lits: Vec<Lit>, origins: Vec<u32>) -> Self {
        Self {
            lits,
            learned: true,
            activity: 0.0,
            lbd: 0,
            origins,
            deleted: false,
        }
    }
}

/// The value assigned to a variable
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LBool {
    True,
    False,
    Undef,
}

impl LBool {
    /// Negate the value
    #[inline]
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn not(self) -> Self {
        match self {
            LBool::True => LBool::False,
            LBool::False => LBool::True,
            LBool::Undef => LBool::Undef,
        }
    }
}

/// Information about a variable assignment
#[derive(Clone, Debug)]
pub(super) struct VarData {
    /// Current assignment (Undef if unassigned)
    pub(super) value: LBool,
    /// Decision level at which this variable was assigned
    pub(super) level: u32,
    /// The clause that implied this assignment (INVALID for decisions)
    pub(super) reason: ClauseRef,
}

impl Default for VarData {
    fn default() -> Self {
        Self {
            value: LBool::Undef,
            level: 0,
            reason: ClauseRef::INVALID,
        }
    }
}

/// Watch list for a literal (two-watched literal scheme)
pub(crate) type WatchList = Vec<ClauseRef>;

/// Unsat core from SAT solver - indices of original clauses that form an unsatisfiable subset
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SatUnsatCore {
    /// Indices of original (non-learned) clauses in the unsat core
    pub(crate) clause_indices: Vec<u32>,
}

/// Result of SAT solving
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveResult {
    /// Satisfiable with the given assignment (variable index -> bool)
    Sat(Vec<bool>),
    /// Unsatisfiable, optionally with an unsat core (original clause indices)
    Unsat(Option<SatUnsatCore>),
    /// Resource limit reached
    Unknown,
}

/// Solver statistics
#[derive(Clone, Debug, Default)]
pub struct SolverStats {
    pub(crate) conflicts: u64,
    pub(crate) decisions: u64,
    pub(crate) propagations: u64,
    pub(crate) learned_clauses: u64,
}
