// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The kernel controls of the `eqsat_rules` gate: what Clean's reference entry
//! accepts and refuses on the replayed family, each refusal beside an accepted
//! control (the gate's module documentation lists them).

use std::time::Instant;

use clean_kernel::ReferenceKernel;

use super::terms::{
    accepted, add_zero_literal, at, band_false_literal, bin, c, conds, cvar, int_ty,
    mul_assoc_terms_literal, mul_const_neg_literal, not, refused, rotl_full_literal, rule,
    satisfiable, sorts, sound, udiv_self_literal, var,
};
use super::{INT_TYPES, SAT_LEMMAS};

/// Run every control on the entry of a kernel that replayed the family.
pub(super) fn kernel_controls(k: &ReferenceKernel) {
    // ── The generated literal is the term trust-cg builds. ──
    let u64_ = int_ty("u64");
    let add_zero = sound(add_zero_literal(0), u64_.clone());
    accepted(
        k,
        &sound(c("EqsatRule.Defs.add_zero"), u64_.clone()),
        &at("EqsatInt.add_zero", "u64"),
        "control: add_zero at u64 against the generated definition",
    );
    let started = Instant::now();
    accepted(
        k,
        &add_zero,
        &at("EqsatInt.add_zero", "u64"),
        "add_zero at u64 against the literal built here",
    );
    eprintln!(
        "eqsat_rules: one check_closed_term of a built literal took {} us",
        started.elapsed().as_micros()
    );
    let rotl_full = sound(rotl_full_literal(true), u64_.clone());
    accepted(
        k,
        &rotl_full,
        &at("EqsatInt.rotl_full", "u64"),
        "rotl_full at u64 against the literal built here",
    );
    accepted(
        k,
        &sound(c("EqsatRule.Defs.band_true"), c("EqsatRule.STy.bool")),
        &c("EqsatInt.band_true"),
        "band_true at bool",
    );
    accepted(
        k,
        &sound(c("EqsatRule.Defs.select_same"), c("EqsatRule.STy.bool")),
        &c("EqsatInt.select_same_bool"),
        "select_same at bool",
    );
    for t in INT_TYPES {
        accepted(
            k,
            &sound(add_zero_literal(0), int_ty(t)),
            &at("EqsatInt.add_zero", t),
            &format!("add_zero at {t}"),
        );
    }

    // ── Negative controls, each beside an accepted control above. ──
    refused(
        k,
        &sound(add_zero_literal(1), u64_.clone()),
        &at("EqsatInt.add_zero", "u64"),
        "add_zero's lemma for (add ?x (const 1)) = ?x",
    );
    refused(
        k,
        &sound(rotl_full_literal(false), u64_.clone()),
        &at("EqsatInt.rotl_full", "u64"),
        "rotl_full's lemma for the rule without its side condition",
    );
    refused(
        k,
        &rotl_full,
        &at("EqsatInt.add_zero", "u64"),
        "add_zero's lemma for rotl_full",
    );
    refused(
        k,
        &add_zero,
        &at("EqsatInt.add_zero", "u32"),
        "add_zero's u32 instance for the u64 statement",
    );
    refused(
        k,
        &sound(c("EqsatRule.Defs.add_zero"), c("EqsatRule.STy.bool")),
        &at("EqsatInt.add_zero", "u64"),
        "add_zero's u64 instance for the statement at bool",
    );

    // ── The statement does not carry the rule's domain. A bool-only rule has
    //    no variable, literal or operator of sort T, so its statement is the
    //    same proposition at every instance type and its lemma proves each
    //    (measured: the entry accepts this). Which types a rule may fire at is
    //    the registry's domain test in trust-cg, not a kernel fact. ──
    accepted(
        k,
        &sound(c("EqsatRule.Defs.band_true"), u64_.clone()),
        &c("EqsatInt.band_true"),
        "band_true's lemma at an instance type outside its domain",
    );

    // ── Direction: a refines proof does not prove the equiv statement. ──
    let u8_ = int_ty("u8");
    let refines_proof = c("EqsatIntControls.udiv_self_refines_u8");
    accepted(
        k,
        &sound(udiv_self_literal("refines"), u8_.clone()),
        &refines_proof,
        "control: (udiv ?x ?x) refines to 1 at u8",
    );
    refused(
        k,
        &sound(udiv_self_literal("equiv"), u8_.clone()),
        &refines_proof,
        "the refines proof for the equiv statement of the same sides",
    );
    refused(
        k,
        &sound(c("EqsatRule.WrongDefs.panic_only_udiv_self"), u8_.clone()),
        &refines_proof,
        "the refines proof for the generated equiv definition",
    );
    accepted(
        k,
        &not(sound(udiv_self_literal("equiv"), u8_.clone())),
        &c("EqsatIntControls.panic_only_udiv_self_u8"),
        "the equiv statement of (udiv ?x ?x) = 1 is refuted at u8",
    );

    // ── Each refutation is the statement it is named for. ──
    for (wrong, ty, refutation) in [
        ("wrong_constant", int_ty("u8"), "wrong_constant_u8"),
        (
            "wrong_operand_order",
            int_ty("u8"),
            "wrong_operand_order_u8",
        ),
        ("wrong_select_arm", int_ty("u8"), "wrong_select_arm_u8"),
        (
            "wrong_select_arm",
            c("EqsatRule.STy.bool"),
            "wrong_select_arm_bool",
        ),
        (
            "wrong_boolean_constant",
            int_ty("u8"),
            "wrong_boolean_constant_u8",
        ),
        (
            "missing_side_condition",
            int_ty("u8"),
            "missing_side_condition_u8",
        ),
        ("wrong_width", int_ty("u16"), "wrong_width_u16"),
        ("wrong_width", int_ty("i16"), "wrong_width_i16"),
        ("wrong_fold", int_ty("u8"), "wrong_fold_u8"),
        (
            "panic_only_udiv_self",
            int_ty("u8"),
            "panic_only_udiv_self_u8",
        ),
        (
            "panic_only_sdiv_neg_one",
            int_ty("i8"),
            "panic_only_sdiv_neg_one_i8",
        ),
    ] {
        let statement = sound(c(&format!("EqsatRule.WrongDefs.{wrong}")), ty);
        let proof = c(&format!("EqsatIntControls.{refutation}"));
        accepted(k, &not(statement.clone()), &proof, refutation);
        refused(
            k,
            &statement,
            &proof,
            &format!("{refutation} offered as a proof of the wrong rule"),
        );
    }
    // The missing side condition is what `missing_side_condition` lacks: the
    // generated wrong literal is the rule built here without it.
    refused(
        k,
        &sound(
            c("EqsatRule.WrongDefs.missing_side_condition"),
            u64_.clone(),
        ),
        &at("EqsatInt.rotl_full", "u64"),
        "rotl_full's lemma for missing_side_condition",
    );

    // ── The refutations at every integer type: the canaries a registry runs
    //    reach the widest type and the pointer-width types. ──
    let bool_ = c("EqsatRule.STy.bool");
    for wrong in [
        "wrong_constant",
        "wrong_operand_order",
        "wrong_select_arm",
        "wrong_boolean_constant",
        "missing_side_condition",
        "wrong_fold",
        "panic_only_udiv_self",
        "panic_only_sdiv_neg_one",
    ] {
        for t in INT_TYPES {
            let statement = sound(c(&format!("EqsatRule.WrongDefs.{wrong}")), int_ty(t));
            let proof = at(&format!("EqsatIntControls.{wrong}_all"), t);
            accepted(
                k,
                &not(statement.clone()),
                &proof,
                &format!("{wrong}_all at {t}"),
            );
            refused(
                k,
                &statement,
                &proof,
                &format!("{wrong}_all at {t} offered as a proof of the wrong rule"),
            );
        }
        // An instance refutes its own type only.
        refused(
            k,
            &not(sound(
                c(&format!("EqsatRule.WrongDefs.{wrong}")),
                int_ty("u64"),
            )),
            &at(&format!("EqsatIntControls.{wrong}_all"), "u32"),
            &format!("{wrong}_all at u32 for the statement at u64"),
        );
    }
    for t in [
        "i16", "i32", "i64", "i128", "isize", "u16", "u32", "u64", "u128", "usize",
    ] {
        accepted(
            k,
            &not(sound(c("EqsatRule.WrongDefs.wrong_width"), int_ty(t))),
            &c(&format!("EqsatIntControls.wrong_width_{t}")),
            &format!("wrong_width refuted at {t}"),
        );
    }
    // `wrong_width` is true at eight bits: no refutation proves otherwise.
    accepted(
        k,
        &sound(c("EqsatRule.WrongDefs.wrong_width"), u8_.clone()),
        &c("EqsatIntControls.wrong_width_holds_u8"),
        "wrong_width holds at u8",
    );
    refused(
        k,
        &not(sound(c("EqsatRule.WrongDefs.wrong_width"), u8_.clone())),
        &c("EqsatIntControls.wrong_width_u16"),
        "wrong_width's u16 refutation for the statement at u8",
    );

    // ── The pointer-width hypothesis: each disjunct of `PbOk` is needed by
    //    one refutation at usize, and nothing but 32 and 64 is admitted. ──
    let usize_ = int_ty("usize");
    for (rule_def, holds_at, holds, refutation) in [
        (
            "ptr64Only",
            "u64",
            "ptr64_only_holds_u64",
            "ptr64_only_not_usize",
        ),
        (
            "ptr32Only",
            "u32",
            "ptr32_only_holds_u32",
            "ptr32_only_not_usize",
        ),
    ] {
        let literal = c(&format!("EqsatIntControls.{rule_def}"));
        accepted(
            k,
            &sound(literal.clone(), int_ty(holds_at)),
            &c(&format!("EqsatIntControls.{holds}")),
            holds,
        );
        accepted(
            k,
            &not(sound(literal.clone(), usize_.clone())),
            &c(&format!("EqsatIntControls.{refutation}")),
            refutation,
        );
        refused(
            k,
            &sound(literal.clone(), usize_.clone()),
            &c(&format!("EqsatIntControls.{holds}")),
            &format!("{holds} for the statement at usize"),
        );
        refused(
            k,
            &not(sound(literal, int_ty(holds_at))),
            &c(&format!("EqsatIntControls.{refutation}")),
            &format!("{refutation} for the statement at {holds_at}"),
        );
    }
    accepted(
        k,
        &not(sound(c("EqsatRule.WrongDefs.wrong_width"), usize_.clone())),
        &c("EqsatIntControls.wrong_width_usize_at_32"),
        "wrong_width refuted at usize through the pointer width 32",
    );
    accepted(
        k,
        &sound(c("EqsatIntControls.notSixteen"), usize_.clone()),
        &c("EqsatIntControls.not_sixteen_holds_usize"),
        "a rule false at sixteen bits is Sound at usize",
    );
    accepted(
        k,
        &not(sound(c("EqsatIntControls.notSixteen"), int_ty("u16"))),
        &c("EqsatIntControls.not_sixteen_fails_u16"),
        "the same rule is refuted at u16",
    );
    refused(
        k,
        &sound(c("EqsatIntControls.notSixteen"), int_ty("u16")),
        &c("EqsatIntControls.not_sixteen_holds_usize"),
        "the usize proof for the statement at u16",
    );

    // ── Satisfiability: the second statement of a rule with a `where`
    //    clause, built here as trust-cg will build it. ──
    for rule_name in SAT_LEMMAS {
        for t in INT_TYPES {
            accepted(
                k,
                &satisfiable(c(&format!("EqsatRule.Defs.{rule_name}")), int_ty(t)),
                &at(&format!("EqsatInt.{rule_name}_sat"), t),
                &format!("{rule_name}_sat at {t}"),
            );
        }
    }
    accepted(
        k,
        &satisfiable(rotl_full_literal(true), u64_.clone()),
        &at("EqsatInt.rotl_full_sat", "u64"),
        "rotl_full_sat at u64 against the literal built here",
    );
    refused(
        k,
        &satisfiable(rotl_full_literal(true), u64_.clone()),
        &at("EqsatInt.rotl_full", "u64"),
        "rotl_full's Sound lemma for its Satisfiable statement",
    );
    refused(
        k,
        &rotl_full,
        &at("EqsatInt.rotl_full_sat", "u64"),
        "rotl_full's Satisfiable lemma for its Sound statement",
    );
    refused(
        k,
        &satisfiable(rotl_full_literal(true), u64_.clone()),
        &at("EqsatInt.rotl_full_sat", "u32"),
        "rotl_full_sat's u32 instance for the u64 statement",
    );
    // A rule whose side conditions contradict each other: `Sound` holds of it
    // (the statement says nothing), `Satisfiable` is refuted, and no
    // satisfiability lemma of another rule is accepted for it.
    let contradictory = c("EqsatIntControls.contradictory");
    accepted(
        k,
        &sound(contradictory.clone(), u64_.clone()),
        &at("EqsatIntControls.contradictory_is_sound", "u64"),
        "a rule with contradictory side conditions is Sound",
    );
    accepted(
        k,
        &not(sound(
            c("EqsatIntControls.contradictorySides"),
            u64_.clone(),
        )),
        &at("EqsatIntControls.contradictory_sides_false", "u64"),
        "its sides are not equal",
    );
    accepted(
        k,
        &not(satisfiable(contradictory.clone(), u64_.clone())),
        &at("EqsatIntControls.contradictory_not_satisfiable", "u64"),
        "and it is not Satisfiable",
    );
    for other in SAT_LEMMAS {
        refused(
            k,
            &satisfiable(contradictory.clone(), u64_.clone()),
            &at(&format!("EqsatInt.{other}_sat"), "u64"),
            &format!("{other}_sat for the contradictory rule"),
        );
    }
    refused(
        k,
        &satisfiable(contradictory.clone(), u64_.clone()),
        &at("EqsatIntControls.contradictory_is_sound", "u64"),
        "the contradictory rule's Sound proof for its Satisfiable statement",
    );
    // Contradictory at one width only: the statement is per type.
    let at8 = c("EqsatIntControls.contradictoryAt8");
    accepted(
        k,
        &not(satisfiable(at8.clone(), u8_.clone())),
        &c("EqsatIntControls.contradictory_at8_not_satisfiable_u8"),
        "contradictory at u8",
    );
    accepted(
        k,
        &satisfiable(at8.clone(), int_ty("u16")),
        &c("EqsatIntControls.contradictory_at8_satisfiable_u16"),
        "satisfiable at u16",
    );
    refused(
        k,
        &satisfiable(at8, u8_.clone()),
        &c("EqsatIntControls.contradictory_at8_satisfiable_u16"),
        "the u16 witness for the statement at u8",
    );

    // ── What the kernel does NOT hold, asserted as measured. ──
    // Direction, for a rule the grammar can state: the registered one-way
    // rule `band_false` with its direction flipped is a true statement and is
    // proved. The entry refuses the refines lemma for it (another
    // proposition), and accepts a proof of it. A rule's direction is held by
    // the rule digest and the checker's `SymOfRefines`, in trust-cg.
    accepted(
        k,
        &sound(band_false_literal("refines"), bool_.clone()),
        &c("EqsatInt.band_false"),
        "control: band_false as registered",
    );
    refused(
        k,
        &sound(band_false_literal("equiv"), bool_.clone()),
        &c("EqsatInt.band_false"),
        "band_false's refines lemma for the equiv statement",
    );
    accepted(
        k,
        &sound(band_false_literal("equiv"), bool_.clone()),
        &c("EqsatIntControls.band_false_as_equiv_is_true"),
        "band_false stated as equiv is provable",
    );
    // A refines statement whose left side is always undefined behaviour holds
    // with a right side that is not a term.
    accepted(
        k,
        &sound(c("EqsatIntControls.udivZeroGarbage"), u64_.clone()),
        &at("EqsatIntControls.refines_ub_left_any_rhs", "u64"),
        "a refines statement with a non-term right side",
    );
    // The entry binds a lemma to the proposition, not to the literal: the
    // `const` flags and `cvar` against `var` do not reach it, and neither
    // does the spelling of a literal with one residue at the type.
    accepted(
        k,
        &sound(mul_assoc_terms_literal(), u64_.clone()),
        &at("EqsatInt.mul_mul_const", "u64"),
        "mul_mul_const's lemma for its eval-free twin (flags cleared, var for cvar)",
    );
    accepted(
        k,
        &sound(mul_const_neg_literal(false, 255), u8_.clone()),
        &c("EqsatIntControls.wrong_width_holds_u8"),
        "control: (mul ?x (const 255)) = (neg ?x) at u8",
    );
    accepted(
        k,
        &sound(mul_const_neg_literal(true, 1), u8_.clone()),
        &c("EqsatIntControls.wrong_width_holds_u8"),
        "the (const 255) lemma for the (const -1) literal at u8: one residue",
    );
    // A literal of another residue is another proposition.
    refused(
        k,
        &sound(mul_const_neg_literal(false, 254), u8_.clone()),
        &c("EqsatIntControls.wrong_width_holds_u8"),
        "the (const 255) lemma for the (const 254) literal at u8",
    );
    // An edit that changes the meaning is refused: the inner operator.
    refused(
        k,
        &sound(
            rule(
                "equiv",
                sorts(&[("t", true), ("t", true), ("t", false)]),
                bin("mul", bin("add", var(2), cvar(0)), cvar(1)),
                bin("mul", var(2), bin("mul", cvar(0), cvar(1))),
                conds(vec![]),
            ),
            u64_.clone(),
        ),
        &at("EqsatInt.mul_mul_const", "u64"),
        "mul_mul_const's lemma for the rule with an inner add",
    );
}
