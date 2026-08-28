// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fidelity pin: the prelude must NOT declare `Eq.rfl`.
//!
//! Commit `95c81b04e` registered `theorem Eq.rfl : ∀ {α : Sort u} {a : α}, Eq a a`
//! in `core_eq/basic.rs` so the elaborator's leading-dot lane could resolve
//! `.rfl` under an expected `Eq` type. Its stated justification — "the
//! `Eq`-namespaced restatement of `rfl` … (Lean 4 `Init/Core`) … a theorem, like
//! upstream" — is false: **Lean 4 has no `Eq.rfl` constant.** Measured on both
//! toolchains installed here (`v4.8.0` and `v4.30.0-rc2`, the corpus version):
//!
//! ```text
//! #check @Eq.rfl                    -- Unknown constant `Eq.rfl`
//! example : (1:Nat) = 1 := Eq.rfl   -- Unknown constant `Eq.rfl`
//! example : (1:Nat) = 1 := .rfl     -- Unknown constant `Eq.rfl`
//!                                   --   (inferred from expected type `1 = 1`)
//! ```
//!
//! Upstream's reflexivity carriers are `rfl` (`@[match_pattern] def rfl`,
//! `Init/Prelude.lean:351`) and `HEq.rfl` (`@[match_pattern] protected def`,
//! `Init/Prelude.lean:540`) — both **definitions**, both already mirrored by
//! Clean as `Declaration::Definition`. The one reflexivity *theorem* in Lean
//! core is `Iff.rfl`, whose type head is `Iff`, not `Eq`. A real Mathlib
//! checkout (7,933 `.lean` files) contains zero occurrences of `Eq.rfl`.
//!
//! Registering it therefore did not buy fidelity, it *cost* fidelity: Clean
//! accepted three programs Lean rejects. It also put the first vacuous
//! `Theorem : Eq a a` into the corpus, which the always-on M4 masquerade gate
//! (`tests_masquerade_gate.rs`) correctly flagged, and moved four `env::tests`
//! constant counts by one.
//!
//! This module pins the absence so a re-land has to re-measure Lean first. If a
//! future Lean release does add `Eq.rfl`, update this test **and** the
//! masquerade-gate reasoning together — the gate flags it by construction.

use super::Environment;
use crate::name::Name;

/// `Eq.rfl` must not be registered by `init_eq` (nor by the full prelude).
#[test]
fn eq_rfl_is_not_in_the_prelude_because_lean_has_no_such_constant() {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    assert!(
        env.get_const(&Name::from_string("Eq.rfl")).is_none(),
        "`Eq.rfl` is not a Lean 4 constant (measured: unknown on v4.8.0 and \
         v4.30.0-rc2); registering it makes Clean accept `.rfl` / `Eq.rfl`, \
         which Lean rejects. Use the root-level `rfl` definition instead."
    );

    let prelude = Environment::with_prelude();
    assert!(
        prelude.get_const(&Name::from_string("Eq.rfl")).is_none(),
        "`Eq.rfl` reached the full prelude — see this module's header before \
         re-landing it"
    );
}

/// The reflexivity carriers Lean *does* have must still be there, with the
/// upstream declaration kind: `rfl` and `HEq.rfl` are definitions, not theorems.
#[test]
fn upstream_reflexivity_carriers_are_definitions_not_theorems() {
    use super::types::ConstantKind;

    let env = Environment::with_prelude();
    for name in ["rfl", "HEq.rfl"] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must be registered (Lean Init/Prelude)"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "`{name}` is a `def` upstream (Init/Prelude.lean); registering a \
             reflexivity carrier as a Theorem puts a vacuous `Eq a a` theorem \
             in the corpus and trips the M4 masquerade gate"
        );
    }
}
