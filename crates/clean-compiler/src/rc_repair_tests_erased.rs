// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The object→erased direction of `release_consuming_unboxes` (X4): an
//! object passed to a `Unit`/`PUnit` parameter, which `to_ir::lower_param`
//! binds erased, reaches the call as `u : Erased := box v`. The pre-boxing
//! call consumed `v` and LCNF RC balanced `v` for it; the cast only reads
//! it. Split out of `rc_repair_tests.rs` (module path
//! `rc_repair::tests::erased`).

use super::super::e2e_support::{compile_closure_of, elaborated_env_with, o0};
use super::super::RcRepairMode;
use super::*;
use crate::pass_manager::PipelineConfig;

/// `f(%0) := let %1 := proj₀ %0; inc %1; let %2 := h(%1); dec %0; ret %2`
/// before boxing, with `h`'s parameter erased; boxing passes `h` the temp
/// `%3 : Erased := box %1` instead. `cast_in_twin` makes `%3` a variable
/// the pre-boxing twin already bound (boxing did not introduce it).
fn erased_slot(cast_in_twin: bool) -> (IRDecl, IRDecl) {
    let proj = |rest: IRBody| {
        vdecl(
            1,
            IRType::Object,
            IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: var(0),
            },
            inc(1, rest),
        )
    };
    let tail = |arg: u32| {
        vdecl(
            2,
            IRType::Object,
            apply("h", vec![var(arg)]),
            dec(0, IRBody::Ret(var(2))),
        )
    };
    let cast = |rest: IRBody| {
        vdecl(
            3,
            IRType::Erased,
            IRExpr::Box {
                ty: IRType::Object,
                arg: var(1),
            },
            rest,
        )
    };
    let pre_body = if cast_in_twin {
        proj(cast(tail(3)))
    } else {
        proj(tail(1))
    };
    let pre = decl(vec![(0, IRType::Object)], IRType::Object, pre_body);
    let boxed = decl(
        vec![(0, IRType::Object)],
        IRType::Object,
        proj(cast(tail(3))),
    );
    (pre, boxed)
}

#[test]
fn an_erasing_cast_that_replaced_a_consumption_releases_the_object() {
    let (pre, boxed) = erased_slot(false);
    let msg = refusal(std::slice::from_ref(&boxed));
    assert!(
        msg.contains("object %1 is consumed 0 times with 1 incs"),
        "{msg}"
    );
    let repaired = rc_repair_boxed(&[pre], vec![boxed], &RcUnmanagedVars::new());
    verify_rc_linearity(&repaired).expect("the erasing cast releases what the call consumed");
    let printed = format!("{:?}", repaired[0].body);
    assert!(printed.contains("Dec { var: VarId(1)"), "{printed}");
}

#[test]
fn an_erasing_cast_the_twin_already_had_releases_nothing() {
    // Mutation control for the rule above: the same cast, bound in the
    // pre-boxing twin, is not boxing's representation change, so the repair
    // adds nothing and the verifier still refuses the leak.
    let (pre, boxed) = erased_slot(true);
    let repaired = rc_repair_boxed(&[pre], vec![boxed], &RcUnmanagedVars::new());
    let printed = format!("{:?}", repaired[0].body);
    assert!(!printed.contains("Dec { var: VarId(1)"), "{printed}");
    let msg = refusal(&repaired);
    assert!(msg.contains("object %1"), "{msg}");
}

/// The non-recursive shape of the measured refusal: a `PUnit` field passed
/// to a `PUnit` parameter (refused before with `object %1 is consumed 0
/// times with 1 incs on path entry`).
const PUNIT_PARAM_SOURCE: &str = "def f (u : PUnit) (n : Nat) : Nat := n + 1\n\
def g (p : PUnit × Nat) : Nat := f p.1 p.2\n";

#[test]
fn a_projected_punit_passed_to_a_punit_parameter_compiles_linear() {
    let env = elaborated_env_with(PUNIT_PARAM_SOURCE);
    for pipeline in [PipelineConfig::default(), o0()] {
        compile_closure_of(&env, &pipeline, RcRepairMode::Enabled, &["g", "f"])
            .unwrap_or_else(|e| panic!("`g` must compile and pass verify_rc_linearity: {e}"));
    }
}
