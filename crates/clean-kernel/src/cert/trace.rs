// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel Operation Tracing for Phase 4 Self-Verification
//!
//! This module implements trace collection for kernel operations, enabling
//! independent verification of type checking results. The trace format captures
//! all operations needed to reconstruct a typing derivation.
//!
//! ## Design Goals
//!
//! 1. **Complete**: Capture all kernel operations (typing, def-eq, declarations)
//! 2. **Verifiable**: Traces can be checked by a minimal standalone verifier
//! 3. **Zero-overhead**: No cost when tracing is disabled (`NullCollector`)
//! 4. **Compact**: Efficient serialization for proof archives
//!
//! ## Usage
//!
//! ```text
//! // Enable tracing for a type checker session
//! let collector = ThreadedCollector::new();
//! checker.set_trace_collector(Some(Arc::new(collector)));
//!
//! // Type check expressions...
//! let ty = checker.infer_type(&expr)?;
//!
//! // Collect trace entries
//! let entries = collector.flush();
//! ```
//!
//! Part of #546: Design trace-checking format for Phase 4 self-verification.

use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use serde::{Deserialize, Serialize};

use super::ProofCert;

/// A single trace entry recording a kernel operation.
///
/// Trace entries capture all operations needed to reconstruct a typing derivation:
/// - Type inference (wraps ProofCert for detailed derivation)
/// - Definitional equality checks with reduction steps
/// - WHNF reduction (not captured by ProofCert)
/// - Declaration additions (inductive types, constants)
/// - Universe constraint solving
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TraceEntry {
    /// Type inference operation (wraps ProofCert).
    ///
    /// This is the primary trace entry for typing operations.
    /// The `expr_hash` allows deduplication; the `cert` contains
    /// the full typing derivation.
    Infer {
        /// Hash of the expression being typed (for deduplication)
        expr_hash: u64,
        /// Certificate witnessing the typing derivation
        cert: ProofCert,
    },

    /// Definitional equality check between two expressions.
    ///
    /// Records whether `lhs` and `rhs` are definitionally equal
    /// and the reduction steps used to establish this.
    DefEq {
        /// Hash of the left-hand side expression
        lhs_hash: u64,
        /// Hash of the right-hand side expression
        rhs_hash: u64,
        /// Reduction steps used (may be empty for trivial equalities)
        steps: Vec<TraceDefEqStep>,
        /// Result of the check
        result: bool,
    },

    /// Weak head normal form reduction.
    ///
    /// ProofCert doesn't capture WHNF reduction steps, so this
    /// entry records them for trace completeness.
    Whnf {
        /// Hash of the input expression
        input_hash: u64,
        /// Hash of the output expression (WHNF)
        output_hash: u64,
        /// Sequence of reduction steps applied
        steps: Vec<ReductionStep>,
    },

    /// Addition of a constant declaration.
    AddConst {
        /// Name of the constant
        name: Name,
        /// Hash of the type expression
        type_hash: u64,
        /// Hash of the value expression (None for axioms)
        value_hash: Option<u64>,
        /// Kind of declaration
        kind: DeclKind,
    },

    /// Addition of an inductive type.
    AddInductive {
        /// Name of the inductive type
        name: Name,
        /// Parameter names
        params: Vec<Name>,
        /// Hash of the type expression
        type_hash: u64,
        /// Constructors: (name, type_hash)
        ctors: Vec<(Name, u64)>,
    },

    /// Universe constraint unification.
    UnifyLevels {
        /// Constraints to solve
        constraints: Vec<(Level, Level)>,
        /// Solution (None if unsolvable)
        result: Option<HashMap<Name, Level>>,
    },

    /// Environment state checkpoint.
    ///
    /// Used for verifying environment consistency at key points.
    EnvCheckpoint {
        /// Number of constants in the environment
        const_count: usize,
        /// Hash of the constant name set
        hash: u64,
    },
}

/// A trace record of a definitional equality step.
///
/// These steps mirror the reduction rules in the kernel.
/// Unlike `super::DefEqStep` (used in ProofCert), this is a flat
/// representation for trace serialization without recursive structure.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TraceDefEqStep {
    /// Reflexivity: e ≡ e
    Refl,
    /// Symmetry: if a ≡ b then b ≡ a
    Symm,
    /// Transitivity: if a ≡ b and b ≡ c then a ≡ c
    Trans,
    /// Beta reduction: (λx.b) a ≡ b[a/x]
    Beta,
    /// Delta reduction (unfold constant)
    Delta(Name),
    /// Zeta reduction: let x := v in b ≡ b[v/x]
    Zeta,
    /// Iota reduction (recursor computation)
    Iota {
        /// Constructor name
        ctor: Name,
        /// Recursor rule index
        rule_idx: u32,
    },
    /// Projection reduction
    Proj {
        /// Structure name
        struct_name: Name,
        /// Field index
        idx: u32,
    },
    /// Congruence: if f ≡ f' and a ≡ a' then f a ≡ f' a'
    Cong,
    /// Eta conversion: f ≡ λx. f x when f : (x : A) → B
    Eta,
    /// Proof irrelevance: if p, q : Prop then p ≡ q
    ProofIrrel,
}

/// A single reduction step for WHNF computation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ReductionStep {
    /// Beta reduction: (λx.b) a → b[a/x]
    Beta,
    /// Delta reduction: unfold constant definition
    Delta(Name),
    /// Zeta reduction: let x := v in b → b[v/x]
    Zeta,
    /// Iota reduction: recursor computation
    Iota {
        /// Constructor name
        ctor: Name,
        /// Recursor rule index
        rule_idx: u32,
    },
    /// Projection: struct.field → value
    Proj {
        /// Structure name
        struct_name: Name,
        /// Field index
        idx: u32,
    },
    /// Nat literal to succ chain
    NatLit,
    /// String literal interpretation
    StringLit,
}

/// Kind of constant declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeclKind {
    /// Axiom (no definition)
    Axiom,
    /// Definition with value
    Definition,
    /// Theorem (definition marked as theorem)
    Theorem,
    /// Opaque definition
    Opaque,
}

/// Trait for collecting kernel operation traces.
///
/// Implementations must be thread-safe since type checking can be parallel.
pub trait TraceCollector: Send + Sync {
    /// Record a trace entry.
    ///
    /// This is called during kernel operations when tracing is enabled.
    fn record(&self, entry: TraceEntry);

    /// Flush all collected entries.
    ///
    /// Returns the entries in order of recording and clears the internal buffer.
    fn flush(&self) -> Vec<TraceEntry>;

    /// Check if tracing is enabled.
    ///
    /// Implementations should return `true` to receive `record` calls.
    /// When this returns `false`, the kernel can skip trace generation entirely.
    fn enabled(&self) -> bool;
}

/// A no-op trace collector for normal operation.
///
/// This collector has zero overhead - `enabled()` returns `false` so
/// the kernel skips all trace generation.
pub struct NullCollector;

impl TraceCollector for NullCollector {
    fn record(&self, _entry: TraceEntry) {
        // No-op
    }

    fn flush(&self) -> Vec<TraceEntry> {
        vec![]
    }

    fn enabled(&self) -> bool {
        false
    }
}

impl Default for NullCollector {
    fn default() -> Self {
        NullCollector
    }
}

/// Thread-safe trace collector for trace mode.
///
/// This collector buffers trace entries in memory and can be flushed
/// to retrieve them. Thread-safe for use with parallel type checking.
pub struct ThreadedCollector {
    entries: Mutex<Vec<TraceEntry>>,
}

impl ThreadedCollector {
    /// Create a new empty collector.
    pub fn new() -> Self {
        ThreadedCollector {
            entries: Mutex::new(Vec::new()),
        }
    }

    /// Create a collector with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        ThreadedCollector {
            entries: Mutex::new(Vec::with_capacity(capacity)),
        }
    }

    /// Get the current number of recorded entries.
    pub fn len(&self) -> usize {
        self.entries
            .lock()
            .expect("invariant: trace entries mutex not poisoned")
            .len()
    }

    /// Check if the collector is empty.
    pub fn is_empty(&self) -> bool {
        self.entries
            .lock()
            .expect("invariant: trace entries mutex not poisoned")
            .is_empty()
    }
}

impl TraceCollector for ThreadedCollector {
    fn record(&self, entry: TraceEntry) {
        self.entries
            .lock()
            .expect("invariant: trace entries mutex not poisoned")
            .push(entry);
    }

    fn flush(&self) -> Vec<TraceEntry> {
        let mut entries = self
            .entries
            .lock()
            .expect("invariant: trace entries mutex not poisoned");
        std::mem::take(&mut *entries)
    }

    fn enabled(&self) -> bool {
        true
    }
}

impl Default for ThreadedCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute a simple hash for an expression (for trace deduplication).
///
/// This uses a fast non-cryptographic hash suitable for deduplication.
/// Collision is acceptable since full expressions can be compared.
pub fn expr_hash(expr: &Expr) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    expr.hash(&mut hasher);
    hasher.finish()
}

/// Arc-wrapped trace collector for sharing across threads.
pub type SharedTraceCollector = Arc<dyn TraceCollector>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_null_collector_disabled() {
        let collector = NullCollector;
        assert!(!collector.enabled());
        collector.record(TraceEntry::EnvCheckpoint {
            const_count: 0,
            hash: 0,
        });
        assert!(collector.flush().is_empty());
    }

    #[test]
    fn test_threaded_collector_basic() {
        let collector = ThreadedCollector::new();
        assert!(collector.enabled());
        assert!(collector.is_empty());

        collector.record(TraceEntry::EnvCheckpoint {
            const_count: 10,
            hash: 12345,
        });
        assert_eq!(collector.len(), 1);

        let entries = collector.flush();
        assert_eq!(entries.len(), 1);
        assert!(collector.is_empty());

        if let TraceEntry::EnvCheckpoint { const_count, hash } = &entries[0] {
            assert_eq!(*const_count, 10);
            assert_eq!(*hash, 12345);
        } else {
            panic!("Expected EnvCheckpoint");
        }
    }

    #[test]
    fn test_threaded_collector_thread_safety() {
        use std::thread;

        let collector = Arc::new(ThreadedCollector::new());
        let handles: Vec<_> = (0..10)
            .map(|i| {
                let c = Arc::clone(&collector);
                thread::spawn(move || {
                    for j in 0..100 {
                        c.record(TraceEntry::EnvCheckpoint {
                            const_count: i * 100 + j,
                            hash: (i * 100 + j) as u64,
                        });
                    }
                })
            })
            .collect();

        for h in handles {
            h.join().unwrap();
        }

        let entries = collector.flush();
        assert_eq!(entries.len(), 1000);
    }

    #[test]
    fn test_decl_kind_serde() {
        // Test serialization roundtrip
        let kinds = vec![
            DeclKind::Axiom,
            DeclKind::Definition,
            DeclKind::Theorem,
            DeclKind::Opaque,
        ];
        for kind in kinds {
            let json = serde_json::to_string(&kind).unwrap();
            let decoded: DeclKind = serde_json::from_str(&json).unwrap();
            assert_eq!(kind, decoded);
        }
    }

    #[test]
    fn test_reduction_step_serde() {
        let steps = vec![
            ReductionStep::Beta,
            ReductionStep::Delta(Name::from_string("foo")),
            ReductionStep::Zeta,
            ReductionStep::Iota {
                ctor: Name::from_string("Nat.succ"),
                rule_idx: 1,
            },
            ReductionStep::Proj {
                struct_name: Name::from_string("Prod"),
                idx: 0,
            },
            ReductionStep::NatLit,
            ReductionStep::StringLit,
        ];
        for step in steps {
            let json = serde_json::to_string(&step).unwrap();
            let decoded: ReductionStep = serde_json::from_str(&json).unwrap();
            assert_eq!(
                format!("{:?}", step),
                format!("{:?}", decoded),
                "Roundtrip failed for {:?}",
                step
            );
        }
    }

    #[test]
    fn test_trace_def_eq_step_serde() {
        // Test serialization roundtrip for TraceDefEqStep
        let steps = vec![
            TraceDefEqStep::Refl,
            TraceDefEqStep::Symm,
            TraceDefEqStep::Trans,
            TraceDefEqStep::Beta,
            TraceDefEqStep::Delta(Name::from_string("my_const")),
            TraceDefEqStep::Zeta,
            TraceDefEqStep::Iota {
                ctor: Name::from_string("List.cons"),
                rule_idx: 2,
            },
            TraceDefEqStep::Proj {
                struct_name: Name::from_string("Sigma"),
                idx: 1,
            },
            TraceDefEqStep::Cong,
            TraceDefEqStep::Eta,
            TraceDefEqStep::ProofIrrel,
        ];
        for step in steps {
            let json = serde_json::to_string(&step).unwrap();
            let decoded: TraceDefEqStep = serde_json::from_str(&json).unwrap();
            assert_eq!(
                format!("{:?}", step),
                format!("{:?}", decoded),
                "Roundtrip failed for {:?}",
                step
            );
        }
    }

    #[test]
    fn test_trace_entry_serde() {
        use crate::level::Level;

        // Test serialization roundtrip for TraceEntry variants
        let entries = vec![
            TraceEntry::EnvCheckpoint {
                const_count: 42,
                hash: 0xDEADBEEF,
            },
            TraceEntry::Whnf {
                input_hash: 123,
                output_hash: 456,
                steps: vec![ReductionStep::Beta, ReductionStep::Zeta],
            },
            TraceEntry::DefEq {
                lhs_hash: 100,
                rhs_hash: 200,
                steps: vec![TraceDefEqStep::Refl],
                result: true,
            },
            TraceEntry::AddConst {
                name: Name::from_string("my_theorem"),
                type_hash: 999,
                value_hash: Some(888),
                kind: DeclKind::Theorem,
            },
            TraceEntry::AddInductive {
                name: Name::from_string("MyType"),
                params: vec![Name::from_string("α")],
                type_hash: 777,
                ctors: vec![(Name::from_string("MyType.mk"), 666)],
            },
            TraceEntry::UnifyLevels {
                constraints: vec![(Level::zero(), Level::succ(Level::zero()))],
                result: None,
            },
        ];
        for entry in entries {
            let json = serde_json::to_string(&entry).unwrap();
            let decoded: TraceEntry = serde_json::from_str(&json).unwrap();
            // Compare Debug output since TraceEntry doesn't derive PartialEq
            assert_eq!(
                format!("{:?}", entry),
                format!("{:?}", decoded),
                "Roundtrip failed for entry"
            );
        }
    }

    #[test]
    fn test_expr_hash_deterministic() {
        use crate::expr::Expr;

        // Test that expr_hash is deterministic
        let expr1 = Expr::sort(Level::zero());
        let expr2 = Expr::sort(Level::zero());
        assert_eq!(expr_hash(&expr1), expr_hash(&expr2));

        // Different expressions should (usually) have different hashes
        let expr3 = Expr::sort(Level::succ(Level::zero()));
        // Note: We don't assert inequality since hash collisions are allowed,
        // but in practice Sort(0) and Sort(1) should hash differently
        let _ = expr_hash(&expr3); // Just ensure it doesn't panic
    }
}
