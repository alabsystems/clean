// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The opt-in stub theory: `SetTheory.*` and the `Fact` class stubs
//! (KR1 slice 1, `docs/DECISIONS.md` R132), and the Mathlib placeholder
//! stubs (`Subgroup`, `Subring`, `Subfield`, `Submonoid`, `RingHom`,
//! `Nat.card`, `Finite`, … — KR1 increment 3, R143).
//!
//! These are value-less constants Clean's prelude used to seed into every
//! environment: 163 `SetTheory.*` symbols (`init_set_theory`, each a
//! `Type u`-typed axiom) and `Fact : Prop → Prop` with `Fact.mk` and
//! `Fact.out` (`init_fact`), the last two asserted propositions. None of them
//! is in Lean's `Init`, and the proven-core plan's KR1 requires the default
//! environment to hold none of them (`data/prelude_axiom_ratchet.json`).
//!
//! R143 moved the 69 Mathlib placeholders
//! (`algebra_substructures::PLACEHOLDER_STUB_NAMES`) here on the same terms:
//! each is a value-less `Type u`-typed (or `Type u → Prop`, `Type u → Nat`,
//! `Nat → Prop`) stand-in that is not Mathlib's object, so a default
//! environment that declares one asserts a symbol it cannot define.
//!
//! F3 also moves the fourteen native IO signatures, two control signatures,
//! and four admission markers here as separate optional fragments. Call
//! `init_io_stub_theory`, `init_control_stub_theory`, or
//! `init_admission_stub_theory` explicitly. The mutable source frontend uses an
//! isolated advice context and requests fragments by emitted kernel references
//! before full registration checking; pure source leaves the checked context
//! free of these axioms. The older `init_stub_theory` initializer below retains
//! its SetTheory/Fact/Mathlib scope.
//!
//! They are not deleted: a caller that wants them opts in with
//! [`Environment::init_stub_theory`] (or one of the two initializers). Some
//! initializers opt in on the caller's behalf: the elaborator's Mathlib
//! prelude providers (`import Mathlib.Data.Set.Basic` and the full-Mathlib
//! provider), and the math overlays `init_graph_theory`, `init_fixed_point`,
//! `init_causal_inference` and `init_computational_geometry`, which call
//! `init_set_theory` themselves. "Opt-in" therefore means "absent from
//! `with_prelude`", not "absent unless asked for by name". Either way, a
//! theorem that rests on one says so by name:
//! [`Environment::stub_theory_axioms_of`] is the per-theorem list,
//! [`Environment::stub_theory_report`] prints it for every theorem whose
//! closure reaches the theory, and `clean check`'s per-declaration "rests on
//! axiom(s)" disclosure lists them like any other non-foundational axiom
//! (`clean-cli`'s `a_stub_theory_axiom_is_disclosed_per_declaration`).

use super::{ConstantKind, EnvError, Environment};
use crate::name::{Name, NameInner};

/// The root namespace of the set-theory stubs.
pub const STUB_THEORY_SET_NAMESPACE: &str = "SetTheory";

/// The `Fact` class stubs.
pub const STUB_THEORY_FACT_NAMES: [&str; 3] = ["Fact", "Fact.mk", "Fact.out"];

/// Whether `name` is a name of the stub theory (a `SetTheory.*` name, or one
/// of [`STUB_THEORY_FACT_NAMES`]). Says nothing about whether the environment
/// holds it, or holds it as an axiom.
#[must_use]
pub fn is_stub_theory_name(name: &Name) -> bool {
    if super::bootstrap_stubs::is_bootstrap_stub_name(name) {
        return true;
    }
    // The root component, and how many components there are.
    let mut cur = name;
    let mut depth = 0usize;
    let mut root: Option<&str> = None;
    loop {
        match cur.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, s) => {
                depth += 1;
                root = Some(&**s);
                cur = parent;
            }
            NameInner::Num(parent, _) => {
                depth += 1;
                root = None;
                cur = parent;
            }
        }
    }
    // `SetTheory` itself is the namespace, not a stub.
    if root == Some(STUB_THEORY_SET_NAMESPACE) && depth >= 2 {
        return true;
    }
    let rendered = name.to_string();
    STUB_THEORY_FACT_NAMES.contains(&rendered.as_str())
        || super::algebra_substructures::PLACEHOLDER_STUB_NAMES
            .iter()
            .any(|family| family.contains(&rendered.as_str()))
}

impl Environment {
    /// Opt in to the stub theory: the `SetTheory.*` constants, the `Fact`
    /// class stubs and the Mathlib placeholders. Idempotent.
    ///
    /// # Errors
    ///
    /// The initializers' own errors.
    pub fn init_stub_theory(&mut self) -> Result<(), EnvError> {
        self.init_set_theory()?;
        self.init_fact()?;
        self.init_mathlib_placeholder_stubs()
    }

    /// Opt in to the Mathlib placeholder stubs alone
    /// (`algebra_substructures::PLACEHOLDER_STUB_NAMES`; R143). Idempotent.
    /// The default prelude declared these until R143.
    ///
    /// # Errors
    ///
    /// The initializers' own errors.
    pub fn init_mathlib_placeholder_stubs(&mut self) -> Result<(), EnvError> {
        self.init_subgroup()?;
        self.init_subring()?;
        self.init_subfield()?;
        self.init_submonoid()?;
        self.init_ring_hom()?;
        self.init_nat_card()?;
        self.init_finite()
    }

    /// The stub theory's axioms this environment holds, sorted by name.
    #[must_use]
    pub fn stub_theory_axioms(&self) -> Vec<Name> {
        let mut out: Vec<Name> = self
            .constants()
            .filter(|c| c.kind == ConstantKind::Axiom && is_stub_theory_name(&c.name))
            .map(|c| c.name.clone())
            .collect();
        out.sort_by_cached_key(Name::to_string);
        out
    }

    /// The stub theory's axioms in `name`'s transitive closure, sorted by
    /// name (empty when it rests on none). `None` when `name` is absent.
    /// `axiom_deps` yields axioms only, so a stub-theory name held as a
    /// definition is walked through, never listed.
    #[must_use]
    pub fn stub_theory_axioms_of(&self, name: &Name) -> Option<Vec<Name>> {
        let mut out: Vec<Name> = self
            .axiom_deps(name)?
            .into_iter()
            .filter(is_stub_theory_name)
            .collect();
        out.sort_by_cached_key(Name::to_string);
        Some(out)
    }

    /// One line per theorem whose closure reaches the stub theory, sorted by
    /// theorem name: `'T' depends on stub-theory axioms: [a, b]`. Empty when
    /// no theorem does (in particular, whenever the theory is not opted in).
    #[must_use]
    pub fn stub_theory_report(&self) -> Vec<String> {
        let mut theorems: Vec<&Name> = self
            .constants()
            .filter(|c| c.kind == ConstantKind::Theorem)
            .map(|c| &c.name)
            .collect();
        theorems.sort_by_cached_key(|n| n.to_string());
        theorems
            .into_iter()
            .filter_map(|t| {
                let axioms = self.stub_theory_axioms_of(t)?;
                if axioms.is_empty() {
                    return None;
                }
                let list = axioms
                    .iter()
                    .map(Name::to_unambiguous_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                Some(format!("'{t}' depends on stub-theory axioms: [{list}]"))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Declaration;
    use crate::expr::{BinderInfo, Expr};

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    /// The default prelude holds none of the stub theory; opting in adds all
    /// of it (control: the theory is not empty, so "none" above is a finding).
    #[test]
    fn test_default_prelude_holds_no_stub_theory_and_opt_in_adds_it() {
        let env = Environment::with_prelude();
        assert_eq!(env.stub_theory_axioms(), Vec::<Name>::new());
        for c in env.constants() {
            assert!(
                !is_stub_theory_name(&c.name),
                "the default prelude holds the stub `{}`",
                c.name
            );
        }
        let mut opted = Environment::with_prelude();
        opted.init_stub_theory().expect("opt in");
        let axioms = opted.stub_theory_axioms();
        assert!(axioms.contains(&n("Fact.out")), "{axioms:?}");
        assert!(axioms.contains(&n("SetTheory.Cardinal")), "{axioms:?}");
        assert_eq!(
            axioms.len(),
            166 + 69,
            "163 SetTheory.* plus Fact, Fact.mk, Fact.out, plus the 69 Mathlib placeholders (R143)"
        );
        // The placeholder list is what the initializers declare: every name
        // on it is an axiom once opted in, and opting in adds no axiom the
        // theory does not name (so the list cannot drift from the code).
        for family in super::super::algebra_substructures::PLACEHOLDER_STUB_NAMES {
            for name in family {
                assert!(axioms.contains(&n(name)), "{name} is declared on opt-in");
            }
        }
        let before: std::collections::BTreeSet<String> = env
            .constants()
            .filter(|c| c.kind == ConstantKind::Axiom)
            .map(|c| c.name.to_string())
            .collect();
        let added: Vec<String> = opted
            .constants()
            .filter(|c| c.kind == ConstantKind::Axiom && !before.contains(&c.name.to_string()))
            .map(|c| c.name.to_string())
            .filter(|name| !axioms.iter().any(|a| a.to_string() == *name))
            .collect();
        assert!(
            added.is_empty(),
            "opting in added axioms outside the stub theory: {added:?}"
        );
    }

    /// Per theorem: a theorem that rests on `Fact.out` prints it; one that
    /// rests on nothing of the theory prints no line.
    #[test]
    fn test_axioms_are_printed_per_theorem() {
        let mut env = Environment::with_prelude();
        env.init_stub_theory().expect("opt in");
        let fact_out = env
            .get_const(&n("Fact.out"))
            .expect("Fact.out")
            .type_
            .clone();
        env.add_decl(Declaration::Theorem {
            name: n("KR1Stub.usesFactOut"),
            level_params: vec![],
            type_: fact_out,
            value: Expr::const_(n("Fact.out"), vec![]),
        })
        .expect("a theorem wrapping Fact.out");
        let true_ = Expr::const_(n("True"), vec![]);
        env.add_decl(Declaration::Theorem {
            name: n("KR1Stub.plain"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, true_.clone(), true_),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::const_(n("True"), vec![]),
                Expr::bvar(0),
            ),
        })
        .expect("a theorem resting on nothing");
        assert_eq!(
            env.stub_theory_axioms_of(&n("KR1Stub.usesFactOut")),
            // Its type cites `Fact`, its value `Fact.out`: both are axioms.
            Some(vec![n("Fact"), n("Fact.out")])
        );
        assert_eq!(env.stub_theory_axioms_of(&n("KR1Stub.plain")), Some(vec![]));
        let report = env.stub_theory_report();
        assert!(
            report.contains(
                &"'KR1Stub.usesFactOut' depends on stub-theory axioms: [Fact, Fact.out]"
                    .to_string()
            ),
            "{report:?}"
        );
        assert!(
            !report.iter().any(|l| l.contains("KR1Stub.plain")),
            "{report:?}"
        );
    }

    /// A stub-theory NAME held as a definition is not an axiom of the theory:
    /// a theorem resting on `SetTheory.kr1Wrap := Fact.out` lists `Fact` and
    /// `Fact.out`, not the wrapper.
    #[test]
    fn test_a_stub_theory_definition_is_not_listed_as_an_axiom() {
        let mut env = Environment::with_prelude();
        env.init_stub_theory().expect("opt in");
        let fact_out = env
            .get_const(&n("Fact.out"))
            .expect("Fact.out")
            .type_
            .clone();
        env.add_decl(Declaration::Definition {
            name: n("SetTheory.kr1Wrap"),
            level_params: vec![],
            type_: fact_out.clone(),
            value: Expr::const_(n("Fact.out"), vec![]),
            is_reducible: false,
        })
        .expect("a stub-theory-named definition");
        env.add_decl(Declaration::Theorem {
            name: n("KR1Stub.throughWrap"),
            level_params: vec![],
            type_: fact_out,
            value: Expr::const_(n("SetTheory.kr1Wrap"), vec![]),
        })
        .expect("a theorem through it");
        assert_eq!(
            env.stub_theory_axioms_of(&n("KR1Stub.throughWrap")),
            Some(vec![n("Fact"), n("Fact.out")])
        );
        assert!(!env.stub_theory_axioms().contains(&n("SetTheory.kr1Wrap")));
    }

    /// A math overlay that calls `init_set_theory` opts in on its caller's
    /// behalf (the module docs say so): after `init_graph_theory` the
    /// `SetTheory.*` axioms are present, while `with_prelude` alone holds none.
    #[test]
    fn test_an_overlay_pulls_the_set_theory_stubs_in() {
        let mut env = Environment::with_prelude();
        assert!(env.stub_theory_axioms().is_empty());
        env.init_graph_theory().expect("graph theory overlay");
        assert!(
            env.stub_theory_axioms().contains(&n("SetTheory.Cardinal")),
            "the overlay pulls the set-theory stubs in"
        );
    }

    #[test]
    fn test_stub_theory_names() {
        assert!(is_stub_theory_name(&n("SetTheory.Aleph0")));
        assert!(is_stub_theory_name(&n("Fact.mk")));
        assert!(!is_stub_theory_name(&n("SetTheory")));
        assert!(!is_stub_theory_name(&n("Set.mem")));
        assert!(!is_stub_theory_name(&n("Factorial")));
        assert!(!is_stub_theory_name(&n("Nat.Fact")));
    }
}
