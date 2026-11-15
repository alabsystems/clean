// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked fresh-allocation preservation of the actual byte-world invariant.
//!
//! Owner selection comes from the active owner's position in the real world.
//! Arbitrary prior allocation history is retained. World validity supplies
//! owner support, not high-water, separation, initialized bytes or provider
//! fidelity. The array16 Alloca consumer separately requires real high-water
//! evidence and the actual layout lookup, then derives allocation and binding.
//! Its endpoint is the real Alloca helper. Site fid/block/pc agreement and a
//! fetched module node remain obligations of a step/run-level consumer.
//! These are operational-profile laws, not native/TLA refinement certificates.

use crate::spec::{SpecError, Specification};

const OR_RIGHT: &str = r"def ir_byte_allocation_world_or_right_v1 (a b : Bool)
  (h : @Eq Bool b Bool.true) : @Eq Bool (Bool.or a b) Bool.true :=
@Bool.rec (fun (x : Bool) => @Eq Bool (Bool.or x b) Bool.true)
  h (@Eq.refl Bool Bool.true) a";

const MEMBER_HEAD: &str = r"def ir_byte_owner_member_head_v1 (owner : Nat) (owners : IRList Nat) :
@Eq Bool (ir_byte_owner_member_v1 owner (@IRList.cons Nat owner owners)) Bool.true :=
ir_eq_cong Bool Bool
  (fun (same : Bool) => Bool.or same (ir_byte_owner_member_v1 owner owners))
  (ir_nat_eqb owner owner) Bool.true (ir_byte_function_nat_eq_self_v1 owner)";

fn and(a: &str, b: &str) -> String {
    format!("(Bool.and {a} {b})")
}

fn left(a: &str, b: &str, proof: &str) -> String {
    format!("(ir_byte_world_and_left_v1 {a} {b} {proof})")
}

fn right(a: &str, b: &str, proof: &str) -> String {
    format!("(ir_byte_world_and_right_v1 {a} {b} {proof})")
}

fn join(a: &str, b: &str, pa: &str, pb: &str) -> String {
    format!("(ir_byte_world_and_intro_v1 {a} {b} {pa} {pb})")
}

fn conjunction(parts: &[(&str, String)]) -> (String, String) {
    let Some((last, prefix)) = parts.split_last() else {
        return ("Bool.true".into(), "(@Eq.refl Bool Bool.true)".into());
    };
    prefix.iter().rev().fold(
        (last.0.into(), last.1.clone()),
        |(tail, proof), (head, head_proof)| {
            (and(head, &tail), join(head, &tail, head_proof, &proof))
        },
    )
}

const OWNERS: &str = "(@IRList.cons Nat owner owners)";
const OLD_MEMORY: &str = "(IRByteMemoryV1.mk allocs bytes allocationCursor)";
const FRESH_MEMORY: &str = "(ir_byte_fresh_memory_v1 allocs bytes base size owner)";
const BEFORE_MACHINE: &str = "(IRMachine.mk (@IRList.cons IRFrame current tail) legacy cursor)";
const PTR_TYPES: &str = "(@IRList.cons IRTy IRTy.ptr_ (@IRList.nil IRTy))";
const EXTENT: &str = "(basePositive : Nat.lt 0 base) (sizePositive : Nat.lt 0 size)
  (bounded : Nat.le (Nat.add base size) ir_byte_limit_v1)";

fn owner_bound() -> (&'static str, String) {
    let bound = "(ir_nat_ltb owner next)";
    let unique = "(Bool.not (ir_byte_owner_member_v1 owner owners))";
    let positive = "(ir_nat_pos owner)";
    let tail = "(ir_byte_owners_valid_v1 owners next)";
    let proof = left(
        bound,
        unique,
        &right(
            positive,
            &and(bound, unique),
            &right(tail, &and(positive, &and(bound, unique)), "valid"),
        ),
    );
    (
        "ir_byte_owner_head_bound_v1",
        format!(
            "def ir_byte_owner_head_bound_v1
  (owner : Nat) (owners : IRList Nat) (next : Nat)
  (valid : @Eq Bool (ir_byte_owners_valid_v1 {OWNERS} next) Bool.true) :
@Eq Bool {bound} Bool.true := {proof}"
        ),
    )
}

fn extent_valid() -> (&'static str, String) {
    let (_, proof) = conjunction(&[
        (
            "(ir_nat_pos base)",
            "(ir_byte_allocation_pos_v1 base basePositive)".into(),
        ),
        (
            "(ir_nat_pos size)",
            "(ir_byte_allocation_pos_v1 size sizePositive)".into(),
        ),
        (
            "(ir_nat_leb (Nat.add base size) ir_byte_limit_v1)",
            "(ir_byte_leb_of_le_v1 (Nat.add base size) ir_byte_limit_v1 bounded)".into(),
        ),
    ]);
    ("ir_byte_fresh_extent_valid_v1", format!("def ir_byte_fresh_extent_valid_v1
  (base size owner : Nat) {EXTENT} :
@Eq Bool (ir_byte_alloc_valid_v1 (IRByteAllocationV1.mk base size owner Bool.true)) Bool.true := {proof}"))
}

fn memory_owners() -> (&'static str, String) {
    let old = format!("(ir_byte_memory_owners_v1 {OLD_MEMORY} {OWNERS} next)");
    let valid = "(ir_byte_alloc_valid_v1 (IRByteAllocationV1.mk base size owner Bool.true))";
    let bound = "(ir_nat_ltb owner next)";
    let member = format!("(ir_byte_owner_member_v1 owner {OWNERS})");
    let support = format!("(Bool.or (ir_nat_eqb owner 0) {member})");
    let (_, proof) = conjunction(&[
        (&old, "before".into()),
        (
            valid,
            "(ir_byte_fresh_extent_valid_v1 base size owner basePositive sizePositive bounded)"
                .into(),
        ),
        (
            bound,
            "(ir_byte_owner_head_bound_v1 owner owners next active)".into(),
        ),
        (
            &support,
            format!(
                "(ir_byte_allocation_world_or_right_v1 (ir_nat_eqb owner 0) {member}
          (ir_byte_owner_member_head_v1 owner owners))"
            ),
        ),
    ]);
    (
        "ir_byte_memory_owners_fresh_v1",
        format!(
            "def ir_byte_memory_owners_fresh_v1
  (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (allocationCursor base size owner : Nat) (owners : IRList Nat) (next : Nat)
  (active : @Eq Bool (ir_byte_owners_valid_v1 {OWNERS} next) Bool.true)
  (before : @Eq Bool {old} Bool.true) {EXTENT} :
@Eq Bool (ir_byte_memory_owners_v1 {FRESH_MEMORY} {OWNERS} next) Bool.true := {proof}"
        ),
    )
}

fn old_world() -> String {
    format!("(@IRByteWorldV1.mk W {OLD_MEMORY} host {OWNERS} next)")
}

fn world_telescope() -> String {
    "(W : Type) (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (allocationCursor : Nat) (host : W) (owner : Nat) (owners : IRList Nat) (next : Nat)
  (current : IRFrame) (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor : Nat)"
        .into()
}

fn world_shape() -> (&'static str, String) {
    let empty = "(ir_nat_eqb (ir_byte_length_v1 IRMemSlot legacy) 0)";
    let count = format!("(ir_nat_eqb (ir_byte_length_v1 IRFrame (@IRList.cons IRFrame current tail)) (ir_byte_length_v1 Nat {OWNERS}))");
    let active = format!("(ir_byte_owners_valid_v1 {OWNERS} next)");
    let memory = format!("(ir_byte_memory_owners_v1 {OLD_MEMORY} {OWNERS} next)");
    let both = and(&active, &memory);
    let suffix = and(&count, &both);
    let remainder = right(empty, &suffix, "before");
    let pair = right(&count, &both, &remainder);
    let updated_memory = format!("(ir_byte_memory_owners_v1 {FRESH_MEMORY} {OWNERS} next)");
    let active_proof = left(&active, &memory, &pair);
    let memory_proof = right(&active, &memory, &pair);
    let (_, proof) = conjunction(&[
        (empty, left(empty, &suffix, "before")),
        (&count, left(&count, &both, &remainder)),
        (&active, active_proof.clone()),
        (&updated_memory, format!("(ir_byte_memory_owners_fresh_v1 allocs bytes allocationCursor base size owner owners next
          {active_proof} {memory_proof} basePositive sizePositive bounded)")),
    ]);
    let world = old_world();
    (
        "ir_byte_world_allocate_shape_v1",
        format!(
            "def ir_byte_world_allocate_shape_v1
  {} (updated : IRFrame) (base size : Nat)
  (before : @Eq Bool (ir_byte_world_valid_v1 W {BEFORE_MACHINE} {world}) Bool.true) {EXTENT} :
@Eq Bool (ir_byte_world_valid_v1 W
  (IRMachine.mk (@IRList.cons IRFrame updated tail) legacy cursor)
  (ir_byte_with_memory_v1 W {world} {FRESH_MEMORY})) Bool.true := {proof}",
            world_telescope()
        ),
    )
}

fn pointer_match() -> (&'static str, String) {
    let (_, proof) = conjunction(&[
        ("Bool.true", "(@Eq.refl Bool Bool.true)".into()),
        (
            "(ir_nat_pos address)",
            "(ir_byte_allocation_pos_v1 address positive)".into(),
        ),
        (
            "(ir_nat_ltb address (ir_nat_pow2 64))",
            "(ir_byte_ltb_of_lt_v1 address ir_byte_limit_v1 bounded)".into(),
        ),
    ]);
    (
        "ir_byte_allocated_pointer_matches_v1",
        format!(
            "def ir_byte_allocated_pointer_matches_v1
  (ctx : IRByteContextV1) (address : Nat)
  (positive : Nat.lt 0 address) (bounded : Nat.lt address ir_byte_limit_v1) :
@Eq Bool (ir_byte_value_matches_v1 ctx IRTy.ptr_ (IRScalar.ptr_ address)) Bool.true := {proof}"
        ),
    )
}

fn pointer_result() -> (&'static str, String) {
    let destinations = "(@IRList.cons Nat destination (@IRList.nil Nat))";
    let values = "(@IRList.cons IRScalar (IRScalar.ptr_ address) (@IRList.nil IRScalar))";
    let world = "(ir_byte_with_memory_v1 W world mem)";
    let expected = format!("(@IRByteConfigV1.running W
      (IRMachine.mk (@IRList.cons IRFrame (ir_frame_advance (ir_frame_set_many current {destinations} {values})) tail) legacy cursor) {world})");
    let guard = format!("(Bool.and (ir_nat_eqb (ir_byte_length_v1 Nat {destinations}) (ir_byte_length_v1 IRScalar {values}))
      (ir_byte_values_match_v1 ctx {PTR_TYPES} {values}))");
    let (_, proof) = conjunction(&[
        ("Bool.true", "(@Eq.refl Bool Bool.true)".into()),
        (
            "(ir_byte_value_matches_v1 ctx IRTy.ptr_ (IRScalar.ptr_ address))",
            "(ir_byte_allocated_pointer_matches_v1 ctx address positive bounded)".into(),
        ),
        ("Bool.true", "(@Eq.refl Bool Bool.true)".into()),
    ]);
    ("ir_byte_memory_result_pointer_v1", format!("def ir_byte_memory_result_pointer_v1
  (W : Type) (ctx : IRByteContextV1) (world : IRByteWorldV1 W) (mem : IRByteMemoryV1)
  (current : IRFrame) (tail : IRList IRFrame) (legacy : IRList IRMemSlot) (cursor destination address : Nat)
  (positive : Nat.lt 0 address) (bounded : Nat.lt address ir_byte_limit_v1) :
@Eq (IRByteConfigV1 W)
  (ir_byte_memory_result_v1 W ctx {BEFORE_MACHINE} world {destinations} {PTR_TYPES} Bool.false
    (IRByteMemoryResultV1.value (IRScalar.ptr_ address) mem)) {expected} :=
ir_byte_case_true_v1 (IRByteConfigV1 W) {guard}
  (@IRByteConfigV1.halted W (IROutcome.type_error IRFault.bad_field) {world})
  {expected} {expected} {proof} (@Eq.refl (IRByteConfigV1 W) {expected})"))
}

fn frame16_sources() -> Vec<(&'static str, String)> {
    let base = "(ir_byte_aligned_base_v1 allocationCursor 8)";
    let end = format!("(Nat.add {base} 16)");
    let ty = "(IRTy.array_ (IRTy.uint_ 8) 16)";
    let layout = format!("(IRByteLayoutV1.mk {ty} 16 1 (@IRList.nil IRTy) (@IRList.nil Nat))");
    let world = old_world();
    let fresh = format!("(ir_byte_fresh_memory_v1 allocs bytes {base} 16 owner)");
    let destinations = "(@IRList.cons Nat destination (@IRList.nil Nat))";
    let values = format!("(@IRList.cons IRScalar (IRScalar.ptr_ {base}) (@IRList.nil IRScalar))");
    let updated = format!("(ir_frame_advance (ir_frame_set_many current {destinations} {values}))");
    let next_machine =
        format!("(IRMachine.mk (@IRList.cons IRFrame {updated} tail) legacy cursor)");
    let next_world = format!("(ir_byte_with_memory_v1 W {world} {fresh})");
    let expected = format!("(@IRByteConfigV1.running W {next_machine} {next_world})");
    let site = format!("(IRByteSiteV1.mk fid block pc 8 convention {PTR_TYPES})");
    let actual = format!("(ir_byte_alloca_exec_v1 W ctx {BEFORE_MACHINE} {world} {destinations} {site} {ty} (@IROption.none Nat))");
    let primitive = format!("(ir_byte_alloc_v1 ctx {ty} 1 8 owner {OLD_MEMORY})");
    let allocated = format!("(IRByteMemoryResultV1.value (IRScalar.ptr_ {base}) {fresh})");
    let lift = format!("(fun (r : IRByteMemoryResultV1) => ir_byte_memory_result_v1 W ctx {BEFORE_MACHINE} {world} {destinations} {PTR_TYPES} Bool.false r)");
    let middle = format!("({lift} {allocated})");
    let common = format!("{} (ctx : IRByteContextV1) (destination fid block pc convention : Nat)
  (cursorPositive : Nat.lt 0 allocationCursor) (room : Nat.lt {end} ir_byte_limit_v1)
  (highWater : ir_byte_high_water_v1 allocs allocationCursor)
  (layoutFound : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx {ty}) (@IROption.some IRByteLayoutV1 {layout}))", world_telescope());
    let positive = "(ir_byte_align_eight_positive_v1 allocationCursor cursorPositive)";
    let base_bound = format!(
        "(@Nat.le_trans (Nat.succ {base}) (Nat.succ {end}) ir_byte_limit_v1
      (@Nat.succ_le_succ {base} {end} (Nat.le_add_right {base} 16)) room)"
    );
    let arguments = "W allocs bytes allocationCursor host owner owners next current tail legacy cursor ctx destination fid block pc convention cursorPositive room highWater layoutFound";
    let proof = format!("@Eq.trans (IRByteConfigV1 W) {actual} {middle} {expected}
  (ir_eq_cong IRByteMemoryResultV1 (IRByteConfigV1 W) {lift} {primitive} {allocated}
    (ir_byte_frame16_typed_allocate_v1 ctx allocs bytes allocationCursor owner cursorPositive room highWater layoutFound))
  (ir_byte_memory_result_pointer_v1 W ctx {world} {fresh} current tail legacy cursor destination {base} {positive} {base_bound})");
    let predicate = "(fun (c : IRByteConfigV1 W) => @IRByteConfigV1.rec W (fun (_ : IRByteConfigV1 W) => Prop)
      (fun (machine : IRMachine) (world : IRByteWorldV1 W) => @Eq Bool (ir_byte_world_valid_v1 W machine world) Bool.true)
      (fun (_ : IROutcome) (_ : IRByteWorldV1 W) => False) c)";
    let valid = format!("(ir_byte_world_allocate_shape_v1 W allocs bytes allocationCursor host owner owners next current tail legacy cursor
      {updated} {base} 16 before {positive} (Nat.zero_lt_succ 15) (@Nat.le_of_lt {end} ir_byte_limit_v1 room))");
    vec![
        ("ir_byte_alloca_frame16_exact_v1", format!("def ir_byte_alloca_frame16_exact_v1 {common} :
@Eq (IRByteConfigV1 W) {actual} {expected} := {proof}")),
        ("ir_byte_alloca_frame16_world_v1", format!("def ir_byte_alloca_frame16_world_v1 {common}
  (before : @Eq Bool (ir_byte_world_valid_v1 W {BEFORE_MACHINE} {world}) Bool.true) :
{predicate} {actual} :=
@Eq.subst (IRByteConfigV1 W) {predicate} {expected} {actual}
  (@Eq.symm (IRByteConfigV1 W) {actual} {expected} (ir_byte_alloca_frame16_exact_v1 {arguments})) {valid}")),
    ]
}

fn laws() -> Vec<(&'static str, String)> {
    let mut out = vec![
        ("ir_byte_allocation_world_or_right_v1", OR_RIGHT.into()),
        ("ir_byte_owner_member_head_v1", MEMBER_HEAD.into()),
        owner_bound(),
        extent_valid(),
        memory_owners(),
        world_shape(),
        pointer_match(),
        pointer_result(),
    ];
    out.extend(frame16_sources());
    out
}

impl Specification {
    pub(super) fn add_eval_ir_byte_allocation_world_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(&source, "Checked actual allocation/SSA-bind world preservation; no assumed post-world, high-water-from-validity or native fidelity.")
                .map_err(|error| match error {
                    SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                    SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                    SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
                    other => other,
                })?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_allocation_world_tests.rs"]
mod tests;
