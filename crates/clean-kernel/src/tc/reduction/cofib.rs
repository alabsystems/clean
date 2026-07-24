// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cofibrations (the face lattice) for cubical Kan operations.
//!
//! A *cofibration* is a face formula over the interval — a proposition built
//! from the atomic faces `(i = 0)` and `(i = 1)`, closed under `∧` (meet) and
//! `∨` (join), with `⊤` (true) and `⊥` (false). Cofibrations carve out the
//! *extent* on which a partial element (a tube) of an `hcomp`/`Glue` is defined.
//!
//! Representation: **disjunctive normal form** — a `Cofib` is an OR of
//! conjunctions of atoms, `(a₁ ∧ … ) ∨ (b₁ ∧ … ) ∨ …`. The empty disjunction is
//! `⊥`; a disjunct with an empty conjunction is `⊤`. This is the dedicated
//! representation chosen in `docs/plans/CUBICAL_COFIB_HCOMP_PLAN.md` (NOT new
//! `ExprKind` variants — that would cost ~40 exhaustive-match sites per face
//! operator). Interval variables are identified by an abstract `u32` id; the
//! bridge that parses a cofibration out of an interval `Expr` lives with the
//! `hcomp` reduction (a later increment) and is kept separate from this pure,
//! self-contained, exhaustively-tested algebra.
//!
//! Soundness: this module is a pure boolean algebra. Its correctness is
//! established by unit tests (`is_true`/`restrict`/`entails`/agreement), and the
//! Kan reductions that consume it are independently type-preservation-checked.

/// An atomic face: a single interval variable constrained to an endpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CofibAtom {
    /// The face `(var = 0)`.
    Eq0(u32),
    /// The face `(var = 1)`.
    Eq1(u32),
}

impl CofibAtom {
    /// The interval variable this atom constrains.
    pub(crate) fn var(self) -> u32 {
        match self {
            CofibAtom::Eq0(v) | CofibAtom::Eq1(v) => v,
        }
    }

    /// The endpoint this atom pins the variable to (`true` = 1, `false` = 0).
    pub(crate) fn value(self) -> bool {
        matches!(self, CofibAtom::Eq1(_))
    }

    /// Whether this atom is satisfied when `var` is assigned `value` (`false`=0,
    /// `true`=1). Returns `None` if the atom constrains a different variable.
    fn satisfied_by(self, var: u32, value: bool) -> Option<bool> {
        match self {
            CofibAtom::Eq0(v) if v == var => Some(!value),
            CofibAtom::Eq1(v) if v == var => Some(value),
            _ => None,
        }
    }
}

/// A cofibration in disjunctive normal form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Cofib {
    /// OR of conjunctions. Each inner `Vec` is an AND of atoms; the outer `Vec`
    /// is the OR. `disjuncts == []` is `⊥`; a `[]` conjunct is `⊤`.
    disjuncts: Vec<Vec<CofibAtom>>,
}

impl Cofib {
    /// `⊤` — the always-true cofibration (one empty conjunction).
    pub(crate) fn top() -> Self {
        Cofib {
            disjuncts: vec![vec![]],
        }
    }

    /// `⊥` — the always-false cofibration (no disjuncts).
    pub(crate) fn bot() -> Self {
        Cofib { disjuncts: vec![] }
    }

    /// The single face `(var = 0)`.
    pub(crate) fn eq0(var: u32) -> Self {
        Cofib {
            disjuncts: vec![vec![CofibAtom::Eq0(var)]],
        }
    }

    /// The single face `(var = 1)`.
    pub(crate) fn eq1(var: u32) -> Self {
        Cofib {
            disjuncts: vec![vec![CofibAtom::Eq1(var)]],
        }
    }

    /// Is this syntactically `⊤`? (Some disjunct is the empty conjunction, which
    /// is satisfied by every assignment.)
    pub(crate) fn is_top(&self) -> bool {
        self.disjuncts.iter().any(|conj| conj.is_empty())
    }

    /// Is this `⊥`? (No disjuncts.)
    pub(crate) fn is_bot(&self) -> bool {
        self.disjuncts.is_empty()
    }

    /// Meet (`∧`). Distributes: `(A ∨ B) ∧ (C ∨ D) = AC ∨ AD ∨ BC ∨ BD`.
    /// Each product conjunction drops to `⊥` if it contains both `(v=0)` and
    /// `(v=1)` (contradiction); duplicate atoms are de-duplicated.
    pub(crate) fn and(&self, other: &Cofib) -> Cofib {
        let mut disjuncts = Vec::new();
        for a in &self.disjuncts {
            for b in &other.disjuncts {
                if let Some(conj) = merge_conjunction(a, b) {
                    disjuncts.push(conj);
                }
            }
        }
        Cofib { disjuncts }.normalized()
    }

    /// Join (`∨`). Concatenates the disjuncts.
    pub(crate) fn or(&self, other: &Cofib) -> Cofib {
        let mut disjuncts = self.disjuncts.clone();
        disjuncts.extend(other.disjuncts.iter().cloned());
        Cofib { disjuncts }.normalized()
    }

    /// Evaluate under a total assignment of interval variables to `{0,1}`
    /// (`assign(var) -> Some(value)`; `None` ⇒ variable unconstrained, so any
    /// atom on it is treated as unsatisfied).
    pub(crate) fn is_true(&self, assign: &impl Fn(u32) -> Option<bool>) -> bool {
        self.disjuncts.iter().any(|conj| {
            conj.iter().all(|atom| {
                assign(atom.var()).is_some_and(|v| atom.satisfied_by(atom.var(), v) == Some(true))
            })
        })
    }

    /// Restrict by substituting `var := value` (`false`=0, `true`=1), simplifying
    /// the DNF: a satisfied atom is absorbed (`⊤`), a falsified atom kills its
    /// conjunct (`⊥`).
    pub(crate) fn restrict(&self, var: u32, value: bool) -> Cofib {
        let mut disjuncts = Vec::new();
        for conj in &self.disjuncts {
            let mut new_conj = Vec::new();
            let mut killed = false;
            for &atom in conj {
                match atom.satisfied_by(var, value) {
                    Some(true) => {} // absorbed (⊤): drop the atom
                    Some(false) => {
                        killed = true; // conjunct becomes ⊥
                        break;
                    }
                    None => new_conj.push(atom), // different variable: keep
                }
            }
            if !killed {
                disjuncts.push(new_conj);
            }
        }
        Cofib { disjuncts }.normalized()
    }

    /// The DNF disjuncts (each an AND of atoms). `[]` is `⊥`; a `[]` conjunct is
    /// `⊤`. Exposed so the `hcomp` overlap-agreement check can restrict heads to
    /// each face of an overlap cofibration.
    pub(crate) fn disjuncts(&self) -> &[Vec<CofibAtom>] {
        &self.disjuncts
    }

    /// All interval variables mentioned.
    pub(crate) fn all_vars(&self) -> Vec<u32> {
        let mut vars: Vec<u32> = self
            .disjuncts
            .iter()
            .flat_map(|conj| conj.iter().map(|a| a.var()))
            .collect();
        vars.sort_unstable();
        vars.dedup();
        vars
    }

    /// Entailment `self ⊑ other`: every assignment satisfying `self` also
    /// satisfies `other`. Decided by enumerating all `2^n` assignments of the
    /// mentioned variables (`n` is small for real cofibrations).
    pub(crate) fn entails(&self, other: &Cofib) -> bool {
        let mut vars = self.all_vars();
        for v in other.all_vars() {
            if !vars.contains(&v) {
                vars.push(v);
            }
        }
        let n = vars.len();
        // 2^n assignments; guard against pathological sizes (return conservative
        // `false`, never a wrong `true`).
        if n > 24 {
            return false;
        }
        for mask in 0u32..(1u32 << n) {
            let assign = |var: u32| -> Option<bool> {
                vars.iter()
                    .position(|&v| v == var)
                    .map(|idx| (mask >> idx) & 1 == 1)
            };
            if self.is_true(&assign) && !other.is_true(&assign) {
                return false;
            }
        }
        true
    }

    /// Canonicalize: drop conjuncts that are unsatisfiable, sort/dedup atoms in
    /// each conjunct, collapse to `⊤` if any conjunct is empty.
    fn normalized(mut self) -> Cofib {
        let mut out = Vec::new();
        for conj in self.disjuncts.drain(..) {
            // `merge_conjunction` with itself sorts+dedups and detects ⊥.
            if let Some(c) = merge_conjunction(&conj, &[]) {
                if c.is_empty() {
                    // ⊤ disjunct subsumes everything.
                    return Cofib::top();
                }
                if !out.contains(&c) {
                    out.push(c);
                }
            }
        }
        Cofib { disjuncts: out }
    }
}

/// Merge two conjunctions into one (`a ∧ b`), returning `None` if the result is
/// contradictory (contains both `(v=0)` and `(v=1)`). Output atoms are sorted
/// and de-duplicated for a canonical form.
fn merge_conjunction(a: &[CofibAtom], b: &[CofibAtom]) -> Option<Vec<CofibAtom>> {
    let mut atoms: Vec<CofibAtom> = a.iter().chain(b.iter()).copied().collect();
    atoms.sort_unstable_by_key(|atom| match atom {
        CofibAtom::Eq0(v) => (*v, 0u8),
        CofibAtom::Eq1(v) => (*v, 1u8),
    });
    atoms.dedup();
    // Contradiction check: same variable constrained to both 0 and 1.
    for w in atoms.windows(2) {
        if w[0].var() == w[1].var() && w[0] != w[1] {
            return None;
        }
    }
    Some(atoms)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build an assignment closure from `(var, value)` pairs.
    fn assignment(pairs: &[(u32, bool)]) -> impl Fn(u32) -> Option<bool> + '_ {
        move |var| pairs.iter().find(|(v, _)| *v == var).map(|(_, b)| *b)
    }

    #[test]
    fn test_cofib_top_bot() {
        assert!(Cofib::top().is_top());
        assert!(!Cofib::top().is_bot());
        assert!(Cofib::bot().is_bot());
        assert!(!Cofib::bot().is_top());
        assert!(Cofib::top().is_true(&assignment(&[])));
        assert!(!Cofib::bot().is_true(&assignment(&[(0, true)])));
    }

    #[test]
    fn test_cofib_atom_satisfaction() {
        // (i=0) is satisfied by i↦0, not by i↦1.
        assert!(Cofib::eq0(0).is_true(&assignment(&[(0, false)])));
        assert!(!Cofib::eq0(0).is_true(&assignment(&[(0, true)])));
        assert!(Cofib::eq1(0).is_true(&assignment(&[(0, true)])));
        assert!(!Cofib::eq1(0).is_true(&assignment(&[(0, false)])));
        // Unassigned variable ⇒ atom unsatisfied.
        assert!(!Cofib::eq0(0).is_true(&assignment(&[])));
    }

    #[test]
    fn test_cofib_or_boundary() {
        // The path boundary (i=0) ∨ (i=1).
        let boundary = Cofib::eq0(0).or(&Cofib::eq1(0));
        assert!(boundary.is_true(&assignment(&[(0, false)])));
        assert!(boundary.is_true(&assignment(&[(0, true)])));
        // It is not ⊤ (an unassigned i satisfies neither).
        assert!(!boundary.is_top());
        assert!(!boundary.is_true(&assignment(&[])));
    }

    #[test]
    fn test_cofib_and_contradiction_is_bot() {
        // (i=0) ∧ (i=1) is unsatisfiable.
        let c = Cofib::eq0(0).and(&Cofib::eq1(0));
        assert!(c.is_bot(), "(i=0) ∧ (i=1) must be ⊥, got {c:?}");
    }

    #[test]
    fn test_cofib_and_distinct_vars() {
        // (i=0) ∧ (j=1) holds exactly at i↦0, j↦1.
        let c = Cofib::eq0(0).and(&Cofib::eq1(1));
        assert!(c.is_true(&assignment(&[(0, false), (1, true)])));
        assert!(!c.is_true(&assignment(&[(0, false), (1, false)])));
        assert!(!c.is_true(&assignment(&[(0, true), (1, true)])));
    }

    #[test]
    fn test_cofib_restrict() {
        // ((i=0) ∨ (j=1)) | i:=0  ⇒  ⊤ (the (i=0) disjunct fires).
        let c = Cofib::eq0(0).or(&Cofib::eq1(1));
        assert!(c.restrict(0, false).is_top());
        // ((i=0) ∨ (j=1)) | i:=1  ⇒  (j=1).
        let r = c.restrict(0, true);
        assert!(r.is_true(&assignment(&[(1, true)])));
        assert!(!r.is_true(&assignment(&[(1, false)])));
        assert!(!r.is_top());
        // (i=0) ∧ (i=1) | i:=0 ⇒ ⊥.
        assert!(Cofib::eq0(0)
            .and(&Cofib::eq1(0))
            .restrict(0, false)
            .is_bot());
    }

    #[test]
    fn test_cofib_entails() {
        // (i=0) ⊑ (i=0) ∨ (i=1).
        assert!(Cofib::eq0(0).entails(&Cofib::eq0(0).or(&Cofib::eq1(0))));
        // (i=0) does NOT entail (i=1).
        assert!(!Cofib::eq0(0).entails(&Cofib::eq1(0)));
        // ⊥ entails anything; everything entails ⊤.
        assert!(Cofib::bot().entails(&Cofib::eq1(0)));
        assert!(Cofib::eq1(0).entails(&Cofib::top()));
        // ⊤ does not entail a proper face.
        assert!(!Cofib::top().entails(&Cofib::eq0(0)));
    }

    #[test]
    fn test_cofib_all_vars() {
        let c = Cofib::eq0(2).or(&Cofib::eq1(0).and(&Cofib::eq1(5)));
        assert_eq!(c.all_vars(), vec![0, 2, 5]);
    }

    #[test]
    fn test_cofib_normalization_dedups() {
        // (i=0) ∨ (i=0) collapses to (i=0).
        let c = Cofib::eq0(0).or(&Cofib::eq0(0));
        assert_eq!(c.disjuncts.len(), 1);
        // A ∨ ⊤ is ⊤.
        assert!(Cofib::eq0(0).or(&Cofib::top()).is_top());
    }
}
