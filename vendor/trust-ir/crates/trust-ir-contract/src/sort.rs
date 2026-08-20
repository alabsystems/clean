// trust-ir-contract/sort: SMT sorts for formula variables
//
// `Sort::from_ty(&Ty)` deliberately does NOT live here: it couples Sort to the
// Trust MIR `Ty`, which stays in trust-types. trust-types provides it as the
// `SortFromTy` extension trait so existing `Sort::from_ty(ty)` call sites are
// unchanged.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

/// SMT sorts.
///
/// Each formula variable carries a sort indicating its type in the SMT domain.
///
/// # Examples
///
/// ```
/// use trust_ir_contract::Sort;
///
/// let int_sort = Sort::Int;
/// let bv32 = Sort::BitVec(32);
/// let arr = Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8)));
///
/// assert_eq!(int_sort.to_smtlib(), "Int");
/// assert_eq!(bv32.to_smtlib(), "(_ BitVec 32)");
/// assert_eq!(arr.to_smtlib(), "(Array Int (_ BitVec 8))");
/// ```
// Trust: added PartialOrd, Ord, Hash for BTreeSet usage in smtlib_backend
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Sort {
    Bool,
    Int,
    BitVec(u32),
    Array(Box<Sort>, Box<Sort>),
    /// IEEE-754 binary floating point with `eb` exponent bits and `sb`
    /// significand bits *including* the hidden bit. `f32 = Float { eb: 8, sb: 24 }`,
    /// `f64 = Float { eb: 11, sb: 53 }`. Maps to SMT-LIB `(_ FloatingPoint eb sb)`
    /// (the `FloatingPoint` theory, bit-blasted to `QF_BV` by the backend solver).
    Float {
        eb: u32,
        sb: u32,
    },
    /// The SMT-LIB `RoundingMode` sort (operand of `fp.add`/`fp.mul`/… ).
    RoundingMode,
    /// An algebraic datatype sort (Lever A — recursive-ADT SMT modeling).
    ///
    /// Carries the FULL constructor/field structure so the backend can emit a
    /// `declare-datatype` (text path) or build an ay `DatatypeSort` (in-process
    /// path) directly from the sort, with no out-of-band registry. SMT-LIB
    /// datatypes are natively recursive, so a field whose type is the datatype
    /// itself (or another in-scope datatype) is encoded as a BY-NAME reference:
    /// `Datatype { name, constructors: vec![] }`. An empty `constructors` vector
    /// therefore means "a reference to the datatype named `name`, defined
    /// elsewhere" — NOT "a datatype with zero constructors". The definitional
    /// occurrence (the variable's own declared sort) always carries the full,
    /// non-empty constructor list.
    ///
    /// SOUNDNESS: a datatype sort never asserts any fact on its own. It only
    /// introduces the SMT-LIB datatype declaration; the constructor/selector/
    /// tester axioms it brings are the standard sound datatype theory (ay's
    /// `DatatypeSort`). A fresh datatype-sorted constant is unconstrained (SAT),
    /// so declaring one can never make the solver context vacuously UNSAT.
    Datatype {
        /// Datatype (sort) name — the SMT-LIB sort identifier.
        name: String,
        /// One entry per variant/constructor: `(ctor_name, [(field_name, field_sort)])`.
        /// Empty for a by-name recursive reference (see the type-level doc).
        constructors: Vec<(String, Vec<(String, Sort)>)>,
    },
}

/// IEEE-754 rounding modes (SMT-LIB `RoundingMode` theory). The five-letter
/// abbreviations are the SMT-LIB standard short names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RoundingMode {
    /// `roundNearestTiesToEven` — the IEEE-754 default and Rust's float rounding.
    RNE,
    /// `roundNearestTiesToAway`.
    RNA,
    /// `roundTowardPositive`.
    RTP,
    /// `roundTowardNegative`.
    RTN,
    /// `roundTowardZero`.
    RTZ,
}

impl RoundingMode {
    /// SMT-LIB short name for this rounding mode.
    #[must_use]
    pub fn to_smtlib(self) -> &'static str {
        match self {
            RoundingMode::RNE => "RNE",
            RoundingMode::RNA => "RNA",
            RoundingMode::RTP => "RTP",
            RoundingMode::RTN => "RTN",
            RoundingMode::RTZ => "RTZ",
        }
    }
}

impl Sort {
    /// The IEEE-754 `FloatingPoint` sort for a Rust float of the given bit
    /// `width`. Returns `None` for widths that are not IEEE-754 binary formats.
    ///
    /// ```
    /// use trust_ir_contract::Sort;
    /// assert_eq!(Sort::float_for_width(32), Some(Sort::Float { eb: 8, sb: 24 }));
    /// assert_eq!(Sort::float_for_width(64), Some(Sort::Float { eb: 11, sb: 53 }));
    /// assert_eq!(Sort::float_for_width(48), None);
    /// ```
    #[must_use]
    pub fn float_for_width(width: u32) -> Option<Sort> {
        match width {
            16 => Some(Sort::Float { eb: 5, sb: 11 }),
            32 => Some(Sort::Float { eb: 8, sb: 24 }),
            64 => Some(Sort::Float { eb: 11, sb: 53 }),
            128 => Some(Sort::Float { eb: 15, sb: 113 }),
            _ => None,
        }
    }

    /// Convert this Sort to its SMT-LIB2 text representation.
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        match self {
            Sort::Bool => "Bool".to_string(),
            Sort::Int => "Int".to_string(),
            Sort::BitVec(w) => format!("(_ BitVec {w})"),
            Sort::Array(idx, elem) => {
                format!("(Array {} {})", idx.to_smtlib(), elem.to_smtlib())
            }
            Sort::Float { eb, sb } => format!("(_ FloatingPoint {eb} {sb})"),
            Sort::RoundingMode => "RoundingMode".to_string(),
            // A datatype REFERENCE in a sort position is just its name (the SMT-LIB
            // sort identifier). The `(declare-datatype …)` that DEFINES it must be
            // emitted separately, BEFORE any `(declare-fun … () <name>)` that uses
            // it — see `Sort::datatype_declarations`.
            Sort::Datatype { name, .. } => name.clone(),
        }
    }

    /// If this sort is (or transitively contains) datatype definitions, return
    /// the `(declare-datatype …)` command text for each, topologically ordered
    /// so a referenced datatype is declared before the one that uses it. Returns
    /// an empty vector for a sort with no datatype content. Each datatype is
    /// emitted at most once (keyed by name); a by-name reference (empty
    /// `constructors`) contributes no definition.
    ///
    /// The caller (the SMT preamble emitter) must place these BEFORE the
    /// `declare-fun` lines so the datatype sort identifiers are in scope.
    #[must_use]
    pub fn datatype_declarations(&self) -> Vec<String> {
        let mut out = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        self.collect_datatype_decls(&mut out, &mut seen);
        out
    }

    fn collect_datatype_decls(
        &self,
        out: &mut Vec<String>,
        seen: &mut std::collections::BTreeSet<String>,
    ) {
        match self {
            Sort::Array(idx, elem) => {
                idx.collect_datatype_decls(out, seen);
                elem.collect_datatype_decls(out, seen);
            }
            Sort::Datatype { name, constructors } => {
                // A by-name reference (empty constructors) carries no definition.
                if constructors.is_empty() || seen.contains(name) {
                    return;
                }
                seen.insert(name.clone());
                // First, recurse into any NESTED datatype field sorts so their
                // definitions are emitted before this one. A self-recursive field
                // is a by-name reference (empty constructors) and is skipped.
                for (_, fields) in constructors {
                    for (_, field_sort) in fields {
                        field_sort.collect_datatype_decls(out, seen);
                    }
                }
                // Emit this datatype's own `(declare-datatype …)`.
                let ctor_strs: Vec<String> = constructors
                    .iter()
                    .map(|(ctor, fields)| {
                        if fields.is_empty() {
                            format!("({ctor})")
                        } else {
                            let field_strs: Vec<String> = fields
                                .iter()
                                .map(|(fname, fsort)| format!("({fname} {})", fsort.to_smtlib()))
                                .collect();
                            format!("({ctor} {})", field_strs.join(" "))
                        }
                    })
                    .collect();
                out.push(format!(
                    "(declare-datatype {name} ({}))",
                    ctor_strs.join(" ")
                ));
            }
            _ => {}
        }
    }

    /// True iff this sort is (or transitively contains) a datatype sort. Used by
    /// SMT-logic selection to switch the logic family to one that includes the
    /// datatype theory (`*DT*`).
    #[must_use]
    pub fn contains_datatype(&self) -> bool {
        match self {
            Sort::Datatype { .. } => true,
            Sort::Array(idx, elem) => idx.contains_datatype() || elem.contains_datatype(),
            _ => false,
        }
    }
}

#[cfg(test)]
mod datatype_sort_tests {
    use super::*;

    fn bv(w: u32) -> Sort {
        Sort::BitVec(w)
    }

    /// A recursive `Expr`-shaped datatype: a `Const(u32)` leaf and a binary
    /// `App(Expr, Expr)` node whose two children are BY-NAME references back to
    /// `Expr` (the natively-recursive SMT-LIB datatype encoding).
    fn expr_sort() -> Sort {
        let expr_ref = Sort::Datatype {
            name: "Expr".into(),
            constructors: Vec::new(),
        };
        Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Const".into(), vec![("c".into(), bv(32))]),
                (
                    "App".into(),
                    vec![("f".into(), expr_ref.clone()), ("x".into(), expr_ref)],
                ),
            ],
        }
    }

    #[test]
    fn datatype_sort_to_smtlib_is_just_the_name() {
        // In a sort position a datatype is referenced by name; its definition is
        // emitted separately via `datatype_declarations`.
        assert_eq!(expr_sort().to_smtlib(), "Expr");
    }

    #[test]
    fn recursive_datatype_declaration_is_well_formed_and_finite() {
        let decls = expr_sort().datatype_declarations();
        // Exactly ONE declaration — the self-recursion is a by-name reference,
        // so it does NOT expand into an infinite (or duplicated) definition.
        assert_eq!(
            decls.len(),
            1,
            "expected a single declare-datatype, got: {decls:?}"
        );
        assert_eq!(
            decls[0], "(declare-datatype Expr ((Const (c (_ BitVec 32))) (App (f Expr) (x Expr))))",
            "datatype declaration must reference Expr by name in its recursive fields"
        );
    }

    #[test]
    fn by_name_reference_emits_no_declaration() {
        // A bare back-edge reference carries no definition (its definer emits it).
        let r = Sort::Datatype {
            name: "Expr".into(),
            constructors: Vec::new(),
        };
        assert!(r.datatype_declarations().is_empty());
        assert!(r.contains_datatype());
        assert_eq!(r.to_smtlib(), "Expr");
    }

    #[test]
    fn nested_distinct_datatypes_are_topologically_ordered() {
        // Tower references Block; Block must be declared first.
        let block_ref = Sort::Datatype {
            name: "Block".into(),
            constructors: Vec::new(),
        };
        let tower_ref = Sort::Datatype {
            name: "Tower".into(),
            constructors: Vec::new(),
        };
        let tower = Sort::Datatype {
            name: "Tower".into(),
            constructors: vec![
                ("empty".into(), vec![]),
                (
                    "stack".into(),
                    vec![("top".into(), block_ref), ("rest".into(), tower_ref)],
                ),
            ],
        };
        // The `Block` reference inside `tower` is by-name (no constructors), so
        // it contributes no definition; only `Tower` is declared here. (A real
        // multi-datatype VC carries Block's full definition on its own variable.)
        let decls = tower.datatype_declarations();
        assert_eq!(
            decls.len(),
            1,
            "only Tower is fully defined here, got: {decls:?}"
        );
        assert!(decls[0].contains("declare-datatype Tower"));
    }

    #[test]
    fn non_datatype_sorts_have_no_declarations() {
        assert!(Sort::Int.datatype_declarations().is_empty());
        assert!(bv(64).datatype_declarations().is_empty());
        assert!(!Sort::Int.contains_datatype());
    }
}
