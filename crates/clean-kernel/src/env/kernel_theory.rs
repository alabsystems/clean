// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel theory profiles: which registered native reducers a check may use.
//!
//! Clean registers native reducers (`ensure_native_reducers`, every
//! [`Environment::new`]) for a much wider set of constants than Lean's kernel
//! computes natively. Lean's kernel computes natively only the `Nat` literal
//! operations (`type_checker.cpp`, `reduce_nat`) and string literals
//! (`string_lit_to_constructor`); everything else it computes by δι, or not at
//! all. Most Clean reducers only ACCELERATE a δι reduction Lean's kernel can
//! perform itself. Some do not: `System.Platform.getIsOSX` is an
//! `@[extern] opaque` in Lean (`Init/System/Platform.lean`), so Lean's kernel
//! can never reduce `System.Platform.isOSX`; Clean's reducer answered it with
//! the BUILD HOST's operating system (`native_reducers_platform.rs`). Measured
//! 2026-09-23 on a Lean-built `.olean` forged with `debug.skipKernelTC`: the
//! `.olean` re-check lanes accepted `forged4_osx : System.Platform.isOSX = true
//! := Eq.refl true`, which `leanchecker` rejects with `(kernel) declaration
//! type mismatch`.
//!
//! [`KernelTheory::Lean`] is the profile the `.olean` re-check lanes run under,
//! and ONLY they. Each of the following sets it, and nothing else does:
//!
//! - every `clean_olean::verify_batch_full` entry point, on its own checker.
//!   Their callers are `clean olean verify-batch --full`, the bootstrap-lane
//!   verifier, the import re-verification metric, and `clean mathverse
//!   per-constant-verify`, which also sets it on its environment once the
//!   trusted closure is resident;
//! - `clean mathverse stamp-verified`, default and `--single-pass`, on the
//!   environment after the closure load;
//! - `clean mathverse stamp-verified --parallel`, on the eager and the
//!   demand-paged PARAGON base;
//! - `mathverse_shard verify-kernel` and its `--corpus` form, for a shard, or
//!   a corpus, whose every constant is Lean 4;
//! - the sharded corpus verifier (`verify::sharded`), after its module load.
//!
//! `clean check` and every other environment stay [`KernelTheory::Extended`].
//! Under [`KernelTheory::Lean`] a native reducer for head `h` fires when `h` is one of Lean's own
//! kernel `Nat` extensions (`LEAN_KERNEL_NAT_EXTENSIONS`), and otherwise only
//! when ALL hold:
//!
//! 1. it is not one of the reducers for Lean's opaque `@[extern]` families —
//!    the platform booleans (`native_reducers_platform.rs`), `Float`
//!    (`native_reducers_float.rs`) and the float→rational bridge
//!    (`native_reducers_float_to_rat.rs`). Lean 4.30's `Float` is
//!    `structure Float where val : floatSpec.float` (`Init/Data/Float.lean`)
//!    over an opaque `floatSpec`, so no `Float` result is reachable by δι.
//!    This rule holds whatever the environment says about those names;
//! 2. `h` is, in THIS environment, a `Definition` that carries a value — a
//!    reducer for an `Opaque`, an `Axiom`, a `Theorem`, a constructor or a
//!    name the environment does not hold adds a reduction rule Lean's kernel
//!    does not have;
//! 3. every constant reachable from `h`'s type and value by δ-unfolding
//!    definitions is present, and none is `Opaque`. A definition whose body is
//!    stuck on an opaque extern is exactly the platform case one level up
//!    (`isOSX := getIsOSX ()`), and it is not only hypothetical: measured with
//!    the pinned Lean 4.30 environment (`Lean.Environment.find?` over every
//!    reducer head, 2026-09-24), `Lean.Name.hash` reaches `mixHash` and
//!    `String.hash`, `Lean.Name.toString` reaches `WellFounded.opaqueFix`, and
//!    every `ISize.*`/`USize.*` head reaches `System.Platform.getNumBits`, all
//!    `opaque` — Lean's kernel can compute none of them, and rule 2 alone
//!    admitted all of them. The walk over-approximates (a constant mentioned in
//!    a branch the reduction never takes still refuses the reducer), which only
//!    sends the term back to ordinary δι.
//!
//! Rules 1-3 say only that Lean's kernel COULD compute the head; they do not
//! say that the reducer computes the SAME value, or even a value of the same
//! type. Measured 2026-09-24 against pinned Lean v4.30.0-rc2: `String.drop`
//! and `String.take` return a `String.Slice` there (`Init/Data/String/TakeDrop.lean`),
//! which remembers the string it was cut from, while Clean's reducers
//! (`native_reducers_string.rs`) return a `String` literal, so the Lean profile
//! proved `String.drop "abc" 1 = String.drop "xbc" 1`; and `trimLeft`,
//! `toLower` and `toUpper` act on Unicode where Lean's act on ASCII only. So one
//! more rule applies to every non-`Nat` head, before rules 2 and 3:
//!
//! 0. the head is in [`LEAN_PROFILE_DIFFERENTIAL_REDUCERS`], the reducers a
//!    differential battery has shown to agree with δι. The battery,
//!    `crates/clean-olean/tests/lean_profile_reducer_differential.rs`, loads the
//!    pinned toolchain's own `Init` `.olean`s, fires every registered reducer on
//!    a battery of literal inputs, and requires each result to be
//!    definitionally equal to the head applied to the same inputs, and of the
//!    same type, in [`KernelTheory::LeanReference`] — Lean's kernel exactly,
//!    with no Clean reducer at all. A reducer that never fired on the battery
//!    is not covered, and is not admitted. Every other reducer is off: the
//!    term falls back to δι, which is what Lean's kernel does.
//!
//! The default profile, [`KernelTheory::Extended`], is unchanged: `clean check`
//! elaboration and every environment that does not opt in keep every reducer.
//! Turning a reducer off is a reduction STRATEGY change that can only make
//! def-eq more conservative: the Lean profile can turn a former acceptance into
//! a rejection, never the reverse.

use std::collections::HashSet;
use std::sync::LazyLock;

use crate::env::{ConstantKind, Environment};
use crate::expr::UsedConstants;
use crate::name::Name;

/// Which reduction theory a kernel check runs in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum KernelTheory {
    /// Clean's extended theory: every registered native reducer may fire.
    #[default]
    Extended,
    /// Lean 4's kernel theory: a native reducer fires only when it accelerates
    /// a δ-unfolding Lean's kernel could perform (see the module docs).
    Lean,
    /// Lean 4's kernel exactly: the `Nat` literal extensions Lean's
    /// `reduce_nat` has, and no other native reducer. The reference the
    /// differential battery compares every admitted reducer against; it runs
    /// in Lean's safe context, like [`Self::Lean`].
    LeanReference,
}

/// Why the Lean profile refuses a registered native reducer.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LeanTheoryExclusion {
    /// The reducer belongs to a family whose head constants are opaque
    /// `@[extern]` in Lean (platform booleans, `Float`, float→rational).
    OpaqueExternFamily,
    /// No differential battery shows the reducer computes what δι computes
    /// (rule 0: it is not in [`LEAN_PROFILE_DIFFERENTIAL_REDUCERS`]).
    NotDifferentiallyChecked,
    /// The head constant is not a value-carrying `Definition` in this
    /// environment, so Lean's kernel could not δ-reduce it at all.
    NoDefinitionBody,
    /// δ-unfolding the head reaches this `Opaque` constant.
    OpaqueInClosure {
        /// The opaque constant reached.
        opaque: Name,
    },
    /// δ-unfolding the head reaches a constant this environment does not hold,
    /// or a definition whose value it does not hold.
    UnavailableInClosure {
        /// The constant that cannot be seen through.
        name: Name,
    },
    /// The δ-closure is larger than `LEAN_THEORY_CLOSURE_CAP`; refused
    /// rather than walked (fail-closed: the term falls back to δι).
    ClosureTooLarge,
}

/// Most constants the rule-3 walk visits for one reducer head before refusing
/// it. The largest head measured in Lean 4.30 (`Lean.Name.toString`) reaches
/// 899 constants.
pub(crate) const LEAN_THEORY_CLOSURE_CAP: usize = 100_000;

/// The `Nat` operations Lean's kernel itself computes on literals, whatever
/// their definitions say: `type_checker::reduce_nat` (`src/kernel/type_checker.cpp`
/// at the pinned v4.30.0-rc2 commit `3dc1a088b6d2`, lines 609-635) handles
/// `Nat.succ` and exactly these fourteen heads. Clean's reducers for them are
/// the same kernel extension, so the Lean profile admits them without rules 2-3
/// (Clean's builtin prelude spells some of them differently from Lean's
/// library, which would otherwise decide the δ-closure walk).
pub(crate) const LEAN_KERNEL_NAT_EXTENSIONS: [&str; 14] = [
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.gcd",
    "Nat.mod",
    "Nat.div",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
];

/// The non-`Nat` reducers the Lean profile admits (rule 0), each one covered
/// by the differential battery
/// `crates/clean-olean/tests/lean_profile_reducer_differential.rs`: over the
/// pinned toolchain's `Init`, it fired on at least one battery input and every
/// result it produced was definitionally equal, in
/// [`KernelTheory::LeanReference`], to the head applied to the same input, at
/// the same type. The battery fails if a name here stops passing, or if a name
/// here is no longer registered. Rules 1-3 still apply to every name here.
pub const LEAN_PROFILE_DIFFERENTIAL_REDUCERS: &[&str] = &[
    "BitVec.sle",
    "BitVec.slt",
    "BitVec.toNat",
    "BitVec.ule",
    "BitVec.ult",
    "Bool.and",
    "Bool.decEq",
    "Bool.not",
    "Bool.or",
    "Bool.xor",
    "Char.isAlpha",
    "Char.isDigit",
    "Char.isLower",
    "Char.isUpper",
    "Char.isWhitespace",
    "Char.toLower",
    "Char.toNat",
    "Char.toUpper",
    "Int.add",
    "Int.mul",
    "Int.natAbs",
    "Int.neg",
    "Int.sub",
    "Int.toNat",
    "Lean.Name.append",
    "Lean.Name.beq",
    "Lean.Name.mkNum",
    "Lean.Name.mkStr",
    "Nat.blt",
    "Nat.pred",
    "String.append",
    "String.decEq",
    "String.isEmpty",
    "String.length",
    "String.singleton",
    "String.utf8ByteSize",
];

static LEAN_PROFILE_DIFFERENTIAL: LazyLock<HashSet<Name>> = LazyLock::new(|| {
    LEAN_PROFILE_DIFFERENTIAL_REDUCERS
        .iter()
        .map(|s| Name::from_string(s))
        .collect()
});

static LEAN_KERNEL_NAT: LazyLock<HashSet<Name>> = LazyLock::new(|| {
    LEAN_KERNEL_NAT_EXTENSIONS
        .iter()
        .map(|s| Name::from_string(s))
        .collect()
});

/// Reducer names registered by the three families whose head constants Lean
/// treats as opaque `@[extern]`. Derived from the registration functions
/// themselves (a scratch environment registers only those families), so the
/// set cannot drift from what `ensure_native_reducers` actually installs.
static OPAQUE_EXTERN_REDUCERS: LazyLock<HashSet<Name>> = LazyLock::new(|| {
    let mut scratch = Environment::default();
    scratch.init_platform_native_reducers();
    scratch.init_float_native_reducers();
    scratch.init_float_to_rat_native_reducers();
    scratch.registered_native_reducer_names().cloned().collect()
});

impl Environment {
    /// The kernel theory this environment's checks run in.
    #[must_use]
    pub fn kernel_theory(&self) -> KernelTheory {
        self.kernel_theory
    }

    /// Select the kernel theory for every check against this environment
    /// (a `TypeChecker` may override it with
    /// [`crate::tc::TypeChecker::set_kernel_theory`]). Not serialized: an
    /// environment read back from disk is [`KernelTheory::Extended`] until its
    /// owner sets it again.
    pub fn set_kernel_theory(&mut self, theory: KernelTheory) {
        self.kernel_theory = theory;
    }

    /// Names of every registered native reducer (diagnostics, the profile
    /// census and the differential battery; iteration order is unspecified).
    pub fn registered_native_reducer_names(&self) -> impl Iterator<Item = &Name> {
        self.native_reducers.keys()
    }

    /// Why [`KernelTheory::Lean`] refuses the native reducer registered for
    /// `name`, or `None` when the Lean profile admits it (module docs, rules
    /// 0-3). Uncached; the type checker memoizes it per checker.
    #[must_use]
    pub fn lean_theory_exclusion(&self, name: &Name) -> Option<LeanTheoryExclusion> {
        if OPAQUE_EXTERN_REDUCERS.contains(name) {
            return Some(LeanTheoryExclusion::OpaqueExternFamily);
        }
        if LEAN_KERNEL_NAT.contains(name) {
            return None;
        }
        if !LEAN_PROFILE_DIFFERENTIAL.contains(name) {
            return Some(LeanTheoryExclusion::NotDifferentiallyChecked);
        }
        self.lean_theory_structural_exclusion(name)
    }

    /// Rules 2 and 3 alone: whether Lean's kernel could compute `name` at all
    /// in THIS environment (a value-carrying definition whose δ-closure is
    /// available and opaque-free). The differential battery asks this of every
    /// registered reducer before it fires any of them.
    #[must_use]
    pub(crate) fn lean_theory_structural_exclusion(
        &self,
        name: &Name,
    ) -> Option<LeanTheoryExclusion> {
        let Some(head) = self.get_const(name) else {
            return Some(LeanTheoryExclusion::NoDefinitionBody);
        };
        let (ConstantKind::Definition, Some(value)) = (head.kind, head.value.as_ref()) else {
            return Some(LeanTheoryExclusion::NoDefinitionBody);
        };
        let mut frontier: HashSet<Name> = HashSet::new();
        head.type_
            .used_constants_dag(UsedConstants::ConstantsOnly, &mut frontier);
        value.used_constants_dag(UsedConstants::ConstantsOnly, &mut frontier);
        let mut visited: HashSet<Name> = HashSet::from([name.clone()]);
        let mut stack: Vec<Name> = frontier.into_iter().collect();
        while let Some(constant) = stack.pop() {
            if !visited.insert(constant.clone()) {
                continue;
            }
            if visited.len() > LEAN_THEORY_CLOSURE_CAP {
                return Some(LeanTheoryExclusion::ClosureTooLarge);
            }
            // Inductive types, constructors, recursors and the quotient
            // primitives are mirrored into the constant table as VALUE-LESS
            // `Definition`s (`inductive_builder.rs`, `ConstantInfo::new`), so
            // their registries are consulted first: each is a leaf that reduces
            // by ι or by the quotient rule, exactly as in Lean's kernel.
            if self.is_family_or_quot(&constant) {
                continue;
            }
            match self.get_const(&constant) {
                Some(ci) => match ci.kind {
                    ConstantKind::Opaque => {
                        return Some(LeanTheoryExclusion::OpaqueInClosure { opaque: constant })
                    }
                    ConstantKind::Definition => {
                        let Some(body) = ci.value.as_ref() else {
                            return Some(LeanTheoryExclusion::UnavailableInClosure {
                                name: constant,
                            });
                        };
                        let mut next = HashSet::new();
                        body.used_constants_dag(UsedConstants::ConstantsOnly, &mut next);
                        stack.extend(next.into_iter().filter(|n| !visited.contains(n)));
                    }
                    // Theorems are proof-irrelevant and axioms are leaves Lean's
                    // kernel does not unfold either.
                    ConstantKind::Theorem | ConstantKind::Axiom => {}
                },
                None => {
                    return Some(LeanTheoryExclusion::UnavailableInClosure { name: constant });
                }
            }
        }
        None
    }

    /// Whether `name` is one of the `Nat` heads Lean's kernel computes on
    /// literals itself (`reduce_nat`), the only reducers
    /// [`KernelTheory::LeanReference`] keeps.
    #[must_use]
    pub fn is_lean_kernel_nat_extension(name: &Name) -> bool {
        LEAN_KERNEL_NAT.contains(name)
    }

    fn is_family_or_quot(&self, name: &Name) -> bool {
        self.get_inductive(name).is_some()
            || self.get_constructor(name).is_some()
            || self.get_recursor(name).is_some()
            || self.get_quot(name).is_some()
    }

    /// The native reducer for `name` that a check running in `theory` may use
    /// (the uncached form of `TypeChecker::native_reducer_for`, which is what
    /// the kernel's reduction path calls): the theory's own rules AND native-
    /// fold authority over the head and every name its reducer recognizes.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn native_reducer_in(
        &self,
        name: &Name,
        theory: KernelTheory,
    ) -> Option<&crate::env::NativeReducerFn> {
        let reducer = self.get_native_reducer(name)?;
        let theory_ok = match theory {
            KernelTheory::Extended => true,
            KernelTheory::Lean => self.lean_theory_exclusion(name).is_none(),
            KernelTheory::LeanReference => LEAN_KERNEL_NAT.contains(name),
        };
        // Authority applies in every theory (`native_fold_authority.rs`).
        let authorized = self.native_fold_authorized(name)
            && super::recognized_argument_names(name)
                .iter()
                .all(|r| self.get_const(r).is_none() || self.native_fold_definition_admitted(r));
        (theory_ok && authorized).then_some(reducer)
    }
}

#[cfg(test)]
#[path = "kernel_theory_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "kernel_theory_level_tests.rs"]
mod level_tests;
