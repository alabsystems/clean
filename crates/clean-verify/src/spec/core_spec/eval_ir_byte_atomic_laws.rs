// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Universal execution and frame laws for the sequential fetch-add model.
//! Success follows from initialized little-endian bytes, the actual canonical
//! layout/live aligned extent checks, and a bounded sum. It is not a premise.
//! These laws do not establish concurrent atomicity or admit atomic IR.

use super::eval_ir_byte_atomic::with_declaration_name;
use crate::spec::{SpecError, Specification};

const RESULT: &str = "IRByteMemoryResultV1";
const U64: &str = "IRTy.uint_ 64";
const LAYOUT: &str = "IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat)";
const ALIGN: &str = "ir_byte_effective_align_v1 8 (ir_byte_layout_align_v1
  (IRByteLayoutV1.mk (IRTy.uint_ 64) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat)))";
const ACTUAL: &str =
    "ir_byte_fetch_add_relaxed_u64_seq_v1 ctx (IRScalar.ptr_ p) (IRScalar.int_ delta) mem";
const EXECUTION: &str = "ir_byte_fetch_add_relaxed_u64_seq_below_v1 ctx mem p n delta
  location_bounded layout_found accessible rep sum_bounded";

const REPRESENTATION_WRITE: &str = r"def ir_byte_u64_rep_write_v1
  (mem : IRByteMemoryV1) (p n : Nat) :
  ir_byte_u64_rep_v1
    (IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 mem)
      (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) p 8 n)
      (ir_byte_mem_next_v1 mem)) p n :=
fun (i : Nat) (inside : Nat.lt i 8) =>
  ir_byte_write_digit_v1 (ir_byte_mem_bytes_v1 mem) p 8 n i inside";

const REPRESENTATION_READ: &str = r"def ir_byte_u64_rep_read_v1
  (mem : IRByteMemoryV1) (p n : Nat)
  (bounded : Nat.lt n ir_byte_limit_v1) (rep : ir_byte_u64_rep_v1 mem p n) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 p)
    (@IROption.some Nat n) :=
@Eq.trans (IROption Nat)
  (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) 8 p)
  (ir_byte_read_word_v1 (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) p 8 n) 8 p)
  (@IROption.some Nat n)
  (ir_byte_read_range_congr_v1 (ir_byte_mem_bytes_v1 mem)
    (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) p 8 n) 8 p
    (fun (i : Nat) (inside : Nat.lt i 8) =>
      @Eq.trans (IROption Nat) (ir_byte_mem_bytes_v1 mem (Nat.add p i))
        (@IROption.some Nat (Nat.mod (Nat.div n (ir_nat_pow2 (Nat.mul 8 i))) 256))
        (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) p 8 n (Nat.add p i))
        (rep i inside)
        (@Eq.symm (IROption Nat)
          (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) p 8 n (Nat.add p i))
          (@IROption.some Nat (Nat.mod (Nat.div n (ir_nat_pow2 (Nat.mul 8 i))) 256))
          (ir_byte_write_digit_v1 (ir_byte_mem_bytes_v1 mem) p 8 n i inside))))
  (ir_byte_read_write_eight_v1 (ir_byte_mem_bytes_v1 mem) p n bounded)";

fn telescope() -> String {
    // Match the operational alignment projection syntactically. Prematurely
    // reducing this to 8 can make elaboration normalize the entire symbolic
    // accessibility check (including subtraction from 2^64).
    format!(
        "(ctx : IRByteContextV1) (mem : IRByteMemoryV1) (p n delta : Nat)
  (location_bounded : Nat.lt p ir_byte_limit_v1)
  (layout_found : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ({U64}))
    (@IROption.some IRByteLayoutV1 ({LAYOUT})))
  (accessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) p 8 ({ALIGN})) Bool.true)
  (rep : ir_byte_u64_rep_v1 mem p n)
  (sum_bounded : Nat.lt (Nat.add n delta) ir_byte_limit_v1)"
    )
}

fn written() -> String {
    "IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 mem)
      (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) p 8 (Nat.add n delta))
      (ir_byte_mem_next_v1 mem)"
        .to_owned()
}

fn expected() -> String {
    format!(
        "IRByteMemoryResultV1.value (IRScalar.int_ n) ({})",
        written()
    )
}

fn trans(ty: &str, left: &str, middle: &str, right: &str, first: &str, second: &str) -> String {
    format!("@Eq.trans ({ty}) ({left}) ({middle}) ({right})\n  ({first})\n  ({second})")
}

fn congr(a: &str, b: &str, function: &str, left: &str, right: &str, proof: &str) -> String {
    format!("ir_eq_cong ({a}) ({b}) ({function}) ({left}) ({right})\n  ({proof})")
}

fn fits(word: &str, bound: &str) -> String {
    format!(
        "ir_byte_u64_value_fits_v1 ctx ({word})
  (ir_byte_ltb_of_lt_v1 ({word}) (ir_nat_pow2 64) ({bound}))"
    )
}

fn component_bound(component: &str, inclusion: &str) -> String {
    format!(
        "@Nat.le_trans (Nat.succ {component}) (Nat.succ (Nat.add n delta)) ir_byte_limit_v1
  (@Nat.succ_le_succ {component} (Nat.add n delta) ({inclusion})) sum_bounded"
    )
}

fn execution_source() -> String {
    let old_bound = component_bound("n", "Nat.le_add_right n delta");
    let delta_bound = component_bound("delta", "Nat.le_add_left delta n");
    let loaded = "IRByteMemoryResultV1.value (IRScalar.int_ n) mem";
    let load = format!("ir_byte_load_v1 ctx ({U64}) (IRScalar.ptr_ p) 8 Bool.false mem");
    let load_at = format!("ir_byte_load_at_v1 ctx ({U64}) p 8 ({ALIGN}) mem");
    let load_proof = trans(
        RESULT,
        &load,
        &load_at,
        loaded,
        &format!(
            "ir_byte_load_dispatch_eight_v1 ctx ({U64}) (IRScalar.ptr_ p) 8 mem ({LAYOUT}) p
  ir_byte_u64_lane_eight_v1 layout_found (ir_byte_canonical_layout_eight_v1 ({U64}))
  (ir_byte_pointer_address_bounded_v1 p location_bounded)"
        ),
        &format!(
            "ir_byte_load_at_rule_v1 ctx ({U64}) p 8 ({ALIGN}) mem n (IRScalar.int_ n)
  accessible (ir_byte_u64_rep_read_v1 mem p n ({old_bound}) rep)
  (@Eq.refl (IROption IRScalar) (@IROption.some IRScalar (IRScalar.int_ n)))
  ({})",
            fits("n", &old_bound)
        ),
    );

    let sum = "Nat.add n delta";
    let store = format!(
        "ir_byte_store_v1 ctx ({U64}) (IRScalar.ptr_ p) (IRScalar.int_ ({sum})) 8 Bool.false mem"
    );
    let store_at =
        format!("ir_byte_store_at_v1 ctx ({U64}) p (IRScalar.int_ ({sum})) 8 ({ALIGN}) mem");
    let stored = format!("IRByteMemoryResultV1.value IRScalar.unit_ ({})", written());
    let store_proof = trans(
        RESULT,
        &store,
        &store_at,
        &stored,
        &format!("ir_byte_store_dispatch_eight_v1 ctx ({U64}) (IRScalar.ptr_ p) (IRScalar.int_ ({sum}))
  8 mem ({LAYOUT}) p ir_byte_u64_lane_eight_v1 layout_found
  (ir_byte_canonical_layout_eight_v1 ({U64})) (ir_byte_pointer_address_bounded_v1 p location_bounded)"),
        &format!("ir_byte_store_at_eight_rule_v1 ctx ({U64}) p (IRScalar.int_ ({sum})) ({ALIGN}) mem ({sum})
  accessible ({}) (@Eq.refl (IROption Nat) (@IROption.some Nat ({sum}))) sum_bounded",
            fits(sum, "sum_bounded")),
    );

    let arithmetic =
        format!("ir_binop_eval IRBinOp.add ({U64}) (IRScalar.int_ n) (IRScalar.int_ delta)");
    let added = format!("IRStepResult.value (IRScalar.int_ ({sum}))");
    let after_arithmetic =
        "ir_byte_fetch_add_after_arithmetic_v1 ctx (IRScalar.ptr_ p) (IRScalar.int_ n) mem";
    let after_load = "ir_byte_fetch_add_after_load_v1 ctx (IRScalar.ptr_ p) (IRScalar.int_ delta)";
    let arithmetic_proof = format!(
        "ir_byte_add_uint_below_v1 64 n delta
  (ir_byte_ltb_of_lt_v1 ({sum}) (ir_nat_pow2 64) sum_bounded)"
    );
    let expected = expected();
    let arithmetic_then_store = trans(
        RESULT,
        &format!("{after_arithmetic} ({arithmetic})"),
        &format!("{after_arithmetic} ({added})"),
        &expected,
        &congr(
            "IRStepResult",
            RESULT,
            after_arithmetic,
            &arithmetic,
            &added,
            &arithmetic_proof,
        ),
        &congr(
            RESULT,
            RESULT,
            "ir_byte_fetch_add_return_old_v1 (IRScalar.int_ n)",
            &store,
            &stored,
            &store_proof,
        ),
    );
    let checked_delta = format!(
        "ir_byte_case_true_v1 {RESULT}
  (ir_byte_value_matches_v1 ctx ({U64}) (IRScalar.int_ delta))
  (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.width_bounded) mem)
  ({after_arithmetic} ({arithmetic})) ({expected})
  ({}) ({arithmetic_then_store})",
        fits("delta", &delta_bound)
    );
    let proof = trans(
        RESULT,
        ACTUAL,
        &format!("{after_load} ({loaded})"),
        &expected,
        &congr(RESULT, RESULT, after_load, &load, loaded, &load_proof),
        &checked_delta,
    );
    format!(
        "def ir_byte_fetch_add_relaxed_u64_seq_below_v1 {} :
  @Eq {RESULT} ({ACTUAL}) ({expected}) :=\n{proof}",
        telescope()
    )
}

fn observation_source(
    suffix: &str,
    ty: &str,
    observe: &str,
    expected_value: &str,
) -> (&'static str, String) {
    let name = match suffix {
        "old" => "ir_byte_fetch_add_relaxed_u64_seq_old_v1",
        "allocations" => "ir_byte_fetch_add_relaxed_u64_seq_allocations_v1",
        _ => "ir_byte_fetch_add_relaxed_u64_seq_cursor_v1",
    };
    let function = format!("fun (result : {RESULT}) => {observe}");
    let proof = congr(RESULT, ty, &function, ACTUAL, &expected(), EXECUTION);
    (
        name,
        format!(
            "def {name} {} :
  @Eq ({ty}) (({function}) ({ACTUAL})) ({expected_value}) :=\n{proof}",
            telescope()
        ),
    )
}

fn read_observation_source(frame: bool) -> (&'static str, String) {
    let (name, extra, base, size, expected_read, read_proof) = if frame {
        (
            "ir_byte_fetch_add_relaxed_u64_seq_frame_v1",
            "(readBase readSize : Nat)
  (apart : Or (Nat.le (Nat.add readBase readSize) p) (Nat.le (Nat.add p 8) readBase))",
            "readBase",
            "readSize",
            "ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) readSize readBase",
            "ir_byte_read_write_disjoint_v1 (ir_byte_mem_bytes_v1 mem) readBase readSize p 8 (Nat.add n delta) apart",
        )
    } else {
        (
            "ir_byte_fetch_add_relaxed_u64_seq_new_v1",
            "",
            "p",
            "8",
            "@IROption.some Nat (Nat.add n delta)",
            "ir_byte_read_write_eight_v1 (ir_byte_mem_bytes_v1 mem) p (Nat.add n delta) sum_bounded",
        )
    };
    let function = format!(
        "fun (result : {RESULT}) => ir_byte_read_word_v1
  (ir_byte_mem_bytes_v1 (ir_byte_fetch_add_memory_v1 result)) {size} {base}"
    );
    let actual = format!("({function}) ({ACTUAL})");
    let middle = format!("({function}) ({})", expected());
    let proof = trans(
        "IROption Nat",
        &actual,
        &middle,
        expected_read,
        &congr(
            RESULT,
            "IROption Nat",
            &function,
            ACTUAL,
            &expected(),
            EXECUTION,
        ),
        read_proof,
    );
    (
        name,
        format!(
            "def {name} {} {extra} :
  @Eq (IROption Nat) ({actual}) ({expected_read}) :=\n{proof}",
            telescope()
        ),
    )
}

pub(super) fn laws() -> Vec<(&'static str, String)> {
    vec![
        ("ir_byte_u64_rep_write_v1", REPRESENTATION_WRITE.to_owned()),
        ("ir_byte_u64_rep_read_v1", REPRESENTATION_READ.to_owned()),
        (
            "ir_byte_fetch_add_relaxed_u64_seq_below_v1",
            execution_source(),
        ),
        observation_source(
            "old",
            "IROption IRScalar",
            "ir_byte_fetch_add_old_v1 result",
            "@IROption.some IRScalar (IRScalar.int_ n)",
        ),
        read_observation_source(false),
        observation_source(
            "allocations",
            "IRList IRByteAllocationV1",
            "ir_byte_mem_allocs_v1 (ir_byte_fetch_add_memory_v1 result)",
            "ir_byte_mem_allocs_v1 mem",
        ),
        observation_source(
            "cursor",
            "Nat",
            "ir_byte_mem_next_v1 (ir_byte_fetch_add_memory_v1 result)",
            "ir_byte_mem_next_v1 mem",
        ),
        read_observation_source(true),
    ]
}

impl Specification {
    pub(super) fn add_eval_ir_byte_atomic_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(
                &source,
                "Checked sequential fetch-add execution from initialized bytes and representation checks; no concurrency or native authority.",
            )
            .map_err(|error| with_declaration_name(name, error))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}
