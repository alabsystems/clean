// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! GATE CLAUSE 4 — the **composition boundary**: the same `add_eval_ir` stage
//! must also build in Clean's Lean-4 production prelude.
//!
//! `Specification::new_eval_ir_prelude_spec` (reached through
//! [`clean_verify::eval_ir::build_prelude_spec_with_stack`]) is a **fifth**
//! specification builder, beside `Specification::new` and the three
//! dependency-scoped flavours cached in `test_utils`. It is the environment
//! Trust binds literal program artifacts in: EvalIR's `IR*` / `ir_*`
//! declarations composed with `Environment::with_prelude`'s notation,
//! typeclasses and logical vocabulary, and *not* the self-verification
//! foundation.
//!
//! **Why this test is here rather than only in the lib target.** Between
//! `62985fe98` and `e2e732f7a` this builder was broken for four commits and two
//! days. Every one of those commits ran an honestly-green gate list —
//! integration targets plus `clippy` and `fmt` — and **none of them built the
//! combined prelude**; the only test that did lived in the `--lib` target,
//! inside the 964-test `spec_paying` shard whose measured wall is ~76 minutes,
//! so nobody ran it in a working loop. The regression was found by a full suite
//! pass, not by a gate.
//!
//! The declaration that broke it, `ir_nat_sub_zero_left`, named the spec
//! foundation's `Eq.cong` — a constant the Lean prelude does not have (Lean
//! spells congruence `congrArg`, with a different argument order). Nothing in
//! the EvalIr bundle can catch that, because the EvalIr bundle *does* carry
//! `Eq.cong`. Only building in both environments can.
//!
//! **The invariant this pins.** Every declaration reachable from
//! `add_eval_ir` may name only vocabulary carried by BOTH environments — `Eq`,
//! `Eq.refl` / `symm` / `trans` / `subst`, `Nat`, `Bool` and their recursors —
//! plus its own `ir_*`. Congruence and the two `Nat.sub` facts the stage needs
//! are therefore proved inside the stage as `ir_eq_cong`,
//! `ir_nat_sub_zero_left` and `ir_nat_sub_succ_succ`.
//!
//! **Measured cost of running it here.** The prelude build is ~12 s and the
//! `eval_ir` target was 13.2 s wall for eight tests, so this clause roughly
//! doubles the cheapest EvalIR gate in the suite and leaves it well under half a
//! minute. That is affordable in a working loop in a way the `spec_paying`
//! shard is not, which is the whole point.

use clean_kernel::Name;
use clean_verify::eval_ir::build_prelude_spec_with_stack;

/// The two authorities have to coexist in one environment: EvalIR's own
/// declarations and the standard prelude classes.
///
/// This mirrors the lib test
/// `eval_ir::tests::prelude_builder_contains_one_evalir_authority_and_standard_classes`
/// deliberately — the point is not a new assertion, it is that this assertion is
/// reachable from a gate a lane can actually run.
#[test]
fn eval_ir_composes_with_the_production_prelude() {
    let spec = build_prelude_spec_with_stack()
        .expect("the EvalIR stage must build in Clean's production prelude, not only in the spec foundation");

    for name in ["IRModule", "ir_init", "ir_step", "HAdd.hAdd", "instHAddNat"] {
        assert!(
            spec.env().get_const(&Name::from_string(name)).is_some(),
            "combined production environment is missing `{name}`"
        );
    }
}

/// The shared-vocabulary rule, stated positively: the congruence and
/// subtraction facts the stage uses are the stage's OWN, present in the
/// composed environment, and the foundation-only names they replaced are
/// absent from it.
///
/// If a future declaration reaches for `Eq.cong` again, the builder above
/// fails; this test says *why* it failed without anyone re-deriving it.
#[test]
fn the_stage_carries_its_own_congruence_and_subtraction_lemmas() {
    let spec = build_prelude_spec_with_stack().expect("prelude composition must build");
    let env = spec.env();

    for name in ["ir_eq_cong", "ir_nat_sub_zero_left", "ir_nat_sub_succ_succ"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` must be proved inside the EvalIR stage — the stage may not \
             borrow congruence or Nat.sub facts from an environment only one of \
             its two build sites has"
        );
    }

    for absent in ["Eq.cong", "nat_sub_zero_left", "nat_sub_succ_succ"] {
        assert!(
            env.get_const(&Name::from_string(absent)).is_none(),
            "`{absent}` is a spec-foundation name and is NOT in the Lean prelude; \
             finding it here means this environment stopped being the production \
             prelude, and the shared-vocabulary rule this file guards would no \
             longer be tested by building in it"
        );
    }
}
