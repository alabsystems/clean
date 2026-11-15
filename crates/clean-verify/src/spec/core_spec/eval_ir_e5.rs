// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal E5 — exact EvalIR images for trust-ir's wide pointers and vtables**
//! (decision memo `docs/handoff/2026-09-23-crystal-decision-memo.md` §23).
//!
//! The M0 producer spells three fat-pointer kinds the cell machine could not
//! execute (memo §21, E-a..E-d): `FatPtr(ContainerLen)` (an `Arc<str>`-style
//! container pointer carrying a LENGTH), `FatPtr(ContainerVtable)` (an
//! `Arc<dyn Tr>`-style container pointer carrying a VTABLE word) and
//! `FatPtr(TraitObject)` (a `&dyn Tr`). The machine change is two lines in
//! `eval_ir_machine.rs` and this stage is what they mean, stated as
//! kernel-checked equations:
//!
//! * **E-a, a cell-machine type.** `ir_ty_shape` puts `containerlen_`,
//!   `containervtable_` and `fatdyn_ k` in class 5 (fat pointer), beside the
//!   legacy `fatptr_`, because their VALUE is the same `IRScalar.fat_ d md`
//!   the reference's `InterpretValueKind::FatPtr { data, metadata }` is. So a
//!   `copy` at them binds a wide value and refuses a thin one
//!   (`ir_e5_copy_*`), which is what the reference's `expect_ty` does across
//!   that boundary.
//! * **E-b, typed metadata.** `ir_ptrmeta_eval` reads the fat value's word at
//!   the node's DECLARED metadata type (`ir_ptrmeta_lane`): `uint_ w` binds a
//!   length, `ptr_` binds a vtable ADDRESS, anything else is the reference's
//!   type error (`eval_ptr_metadata` refuses a non-canonical metadata type).
//!   `ir_e5_ptrmeta_mt_is_read` is the witness that the slot is read — it is the
//!   replacement for the retired `ir_exec_ptrmeta_mt_irrelevant`.
//! * **E-c, the vtable image.** A vtable is a READ-ONLY region of cells laid
//!   out as rustc's `tcx.vtable_allocation(source, principal)` lays it out:
//!   `[drop_in_place, size, align, methods..]`, one pointer-sized word per
//!   cell at byte offsets `0, 8, 16, 24, ..` (`ir_vtable_cells`). D14's align
//!   read (`ptr_metadata .. to ptr`, `gep i8 +16`, `load usize`) returns the
//!   align word from such a region (`ir_vtable_align_load`), and a store the
//!   region does not contain leaves every slot as it was
//!   (`ir_vtable_slot_frame_store`) — the EvalIR half of "read-only". The
//!   region is a HEAP fact (the caller's `mem0`, constrained by a
//!   representation premise), never a module global: the producer's
//!   `__trust_vtable__..` globals still carry no initializer (a producer item),
//!   and a global form with no producer would be a capability with no caller.
//! * **E-d, wide-pointer `icmp`.** Measured against the authority, not
//!   assumed: trust-ir's reference interpreter at the pinned rev `dcc5b9a3`
//!   refuses `icmp` on ANY non-integer operand (`eval_icmp` ->
//!   `expect_int_value`, a `type_error`), and so does the Lean semantics
//!   (`semICmpInst`: "ICmp: non-integer operands"). The memo's §21 reading
//!   ("the reference compares data and metadata") is refuted by both. The
//!   exact image is therefore the HALT, which the machine already takes
//!   (`ir_icmp_eq`'s fat arms are `type_error not_int`); `ir_e5_icmp_*` pin it
//!   at every operand pair so it cannot drift into an answer.
//!
//! Everything here is `Eq.refl`, `Eq.subst` or `Eq.trans` over the registered
//! semantics: zero axiom dependencies, `DerivedProved`. Registration order:
//! after `add_eval_ir_lzd_fresh` (`ir_mem_lookup_update_skip`), at the end of
//! both the EvalIr bundle and `STAGES`.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The E5 declarations, in registration order.
pub const E5_NAMES: &[&str] = &[
    "ir_e5_ptrmeta_mt_is_read",
    "ir_e5_ptrmeta_len_word",
    "ir_e5_ptrmeta_noncanonical_refused",
    "ir_e5_ptrmeta_thin_unit",
    "ir_e5_copy_containerlen",
    "ir_e5_copy_containervtable",
    "ir_e5_copy_fatdyn",
    "ir_e5_copy_fat_refuses_thin",
    "ir_e5_icmp_eq_containerlen_refused",
    "ir_e5_icmp_ne_containerlen_refused",
    "ir_e5_icmp_eq_containervtable_refused",
    "ir_e5_icmp_ne_containervtable_refused",
    "ir_e5_icmp_eq_fatdyn_refused",
    "ir_e5_icmp_ne_fatdyn_refused",
    "ir_vtable_slot",
    "ir_vtable_method_cells",
    "ir_vtable_cells",
    "ir_vtable_size_load",
    "ir_vtable_align_load",
    "ir_vtable_slot_frame_store",
    "ir_e5_d14_gep",
];

const FAULT_NOT_INT: &str = "(IRStepResult.fault (IROutcome.type_error IRFault.not_int))";
const FAULT_NOT_PTR: &str = "(IRStepResult.fault (IROutcome.type_error IRFault.not_ptr))";

/// `(source, description)`, positionally paired with [`E5_NAMES`].
fn decls() -> Vec<(String, &'static str)> {
    let mut out: Vec<(String, &'static str)> = vec![
        (
            "def ir_e5_ptrmeta_mt_is_read (d : Nat) (v : Nat) : Eq IRStepResult \
             (ir_ptrmeta_eval IRTy.ptr_ (IRScalar.fat_ d v)) \
             (IRStepResult.value (IRScalar.ptr_ v)) := \
             Eq.refl IRStepResult (IRStepResult.value (IRScalar.ptr_ v))"
                .to_string(),
            "ir_e5_ptrmeta_mt_is_read: a fat value's metadata word read at the thin pointer type \
             is the vtable ADDRESS `ptr_ v`, where the pre-E5 arm answered `int_ v` at every type. \
             That is why `ptrmetadata.mt` is a relevant-by-design field of the adequacy grid and \
             no longer an irrelevance row. DerivedProved, zero axiom_deps.",
        ),
        (
            "def ir_e5_ptrmeta_len_word (w : Nat) (d : Nat) (n : Nat) : Eq IRStepResult \
             (ir_ptrmeta_eval (IRTy.uint_ w) (IRScalar.fat_ d n)) \
             (IRStepResult.value (IRScalar.int_ n)) := \
             Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ n))"
                .to_string(),
            "ir_e5_ptrmeta_len_word: at an unsigned metadata type the word is the LENGTH, bound as \
             an integer exactly as before E5 — the Str/Slice/ContainerLen arm, and the reason \
             every module minted before E5 keeps its step. DerivedProved, zero axiom_deps.",
        ),
        (
            format!(
                "def ir_e5_ptrmeta_noncanonical_refused (w : Nat) (d : Nat) (m : Nat) : \
                 Eq IRStepResult (ir_ptrmeta_eval (IRTy.int_ w) (IRScalar.fat_ d m)) \
                 {FAULT_NOT_PTR} := Eq.refl IRStepResult {FAULT_NOT_PTR}"
            ),
            "ir_e5_ptrmeta_noncanonical_refused: a SIGNED metadata type is no kind's canonical \
             metadata type (trust-ir `PointerMetadataShape::metadata_ty`: a pointer-sized \
             UNSIGNED length or `Ty::Ptr`), and the reference's `eval_ptr_metadata` raises a \
             type_error for it; so does the model. DerivedProved, zero axiom_deps.",
        ),
        (
            "def ir_e5_ptrmeta_thin_unit (mt : IRTy) (a : Nat) : Eq IRStepResult \
             (ir_ptrmeta_eval mt (IRScalar.ptr_ a)) (IRStepResult.value IRScalar.unit_) := \
             Eq.refl IRStepResult (IRStepResult.value IRScalar.unit_)"
                .to_string(),
            "ir_e5_ptrmeta_thin_unit: the THIN arm is unchanged by E5 and still consults no \
             type: a thin pointer's metadata is unit at every declared type. The reference also \
             requires the declared type to be `()` there; that check is the machine's \
             pre-existing coarseness on thin pointers, not an E5 row. DerivedProved, zero \
             axiom_deps.",
        ),
    ];
    for (name, ty, binders, what) in [
        (
            "ir_e5_copy_containerlen",
            "IRTy.containerlen_",
            "",
            "container_len",
        ),
        (
            "ir_e5_copy_containervtable",
            "IRTy.containervtable_",
            "",
            "container_vtable",
        ),
        (
            "ir_e5_copy_fatdyn",
            "(IRTy.fatdyn_ k)",
            "(k : Nat) ",
            "dyn.k",
        ),
    ] {
        out.push((
            format!(
                "def {name} {binders}(d : Nat) (md : Nat) : Eq IRStepResult \
                 (ir_copy_eval {ty} (IRScalar.fat_ d md)) \
                 (IRStepResult.value (IRScalar.fat_ d md)) := \
                 Eq.refl IRStepResult (IRStepResult.value (IRScalar.fat_ d md))"
            ),
            match what {
                "container_len" => {
                    "ir_e5_copy_containerlen: `copy fatptr<container_len>` binds the wide value \
                     it is given — the kind is shape class 5, the class `IRScalar.fat_` \
                     inhabits. Before E5 it was class 10, which no value inhabits, so the copy \
                     halted type_error where the reference proceeds. DerivedProved, zero \
                     axiom_deps."
                }
                "container_vtable" => {
                    "ir_e5_copy_containervtable: `copy fatptr<container_vtable>` binds the wide \
                     value (class 5). DerivedProved, zero axiom_deps."
                }
                _ => {
                    "ir_e5_copy_fatdyn: `copy fatptr<dyn.k>` binds the wide value at every \
                     trait id (class 5) — D14's `%46 = copy fatptr<dyn..> %45` in \
                     `Environment::get_const`. DerivedProved, zero axiom_deps."
                }
            },
        ));
    }
    out.push((
        format!(
            "def ir_e5_copy_fat_refuses_thin (a : Nat) : Eq IRStepResult \
             (ir_copy_eval IRTy.containervtable_ (IRScalar.ptr_ a)) {FAULT_NOT_PTR} := \
             Eq.refl IRStepResult {FAULT_NOT_PTR}"
        ),
        "ir_e5_copy_fat_refuses_thin: a THIN pointer is not a wide one: copying it at a fat \
         kind faults, as the reference's expect_ty does (a `Ptr` value against a `FatPtr` \
         type). DerivedProved, zero axiom_deps.",
    ));
    for (name, op, ty, binders) in [
        (
            "ir_e5_icmp_eq_containerlen_refused",
            "eq_",
            "IRTy.containerlen_",
            "",
        ),
        (
            "ir_e5_icmp_ne_containerlen_refused",
            "ne_",
            "IRTy.containerlen_",
            "",
        ),
        (
            "ir_e5_icmp_eq_containervtable_refused",
            "eq_",
            "IRTy.containervtable_",
            "",
        ),
        (
            "ir_e5_icmp_ne_containervtable_refused",
            "ne_",
            "IRTy.containervtable_",
            "",
        ),
        (
            "ir_e5_icmp_eq_fatdyn_refused",
            "eq_",
            "(IRTy.fatdyn_ k)",
            "(k : Nat) ",
        ),
        (
            "ir_e5_icmp_ne_fatdyn_refused",
            "ne_",
            "(IRTy.fatdyn_ k)",
            "(k : Nat) ",
        ),
    ] {
        out.push((
            format!(
                "def {name} {binders}(a : IRScalar) (b : IRScalar) : Eq IRStepResult \
                 (ir_icmp_eval IRICmpOp.{op} {ty} a b) {FAULT_NOT_INT} := \
                 Eq.refl IRStepResult {FAULT_NOT_INT}"
            ),
            "ir_e5_icmp_*_refused: `icmp` at a wide-pointer type halts type_error at EVERY \
             operand pair — the exact image of the authority, measured: trust-ir's reference \
             interpreter (`eval_icmp` -> `expect_int_value`) and its Lean semantics \
             (`semICmpInst`) both refuse `icmp` on a non-integer operand, so the three \
             `PartialEq::eq` bodies whose `Arc::ptr_eq` fast path is `icmp eq \
             fatptr<container_len>` halt there in every executor. DerivedProved, zero axiom_deps.",
        ));
    }
    out.extend([
        (
            "def ir_vtable_slot (mem : IRList IRMemSlot) (a : Nat) (v : IRScalar) : Prop := \
             Eq (IROption IRMemSlot) (ir_mem_lookup mem a) \
             (IROption.some IRMemSlot (IRMemSlot.mk a v Bool.true))"
                .to_string(),
            "ir_vtable_slot mem a v: the heap holds a LIVE cell at address `a` carrying `v` — one \
             word of a vtable image. A representation premise states one per slot a body reads; \
             this is a Prop, never a Bool, because it constrains an ABSTRACT caller-supplied heap.",
        ),
        (
            "def ir_vtable_method_cells (a : Nat) (ms : IRList IRScalar) : IRList IRMemSlot := \
             IRList.rec IRScalar (fun (_ : IRList IRScalar) => Nat -> IRList IRMemSlot) \
             (fun (_ : Nat) => IRList.nil IRMemSlot) \
             (fun (m : IRScalar) (_ : IRList IRScalar) (ih : Nat -> IRList IRMemSlot) => \
             fun (b : Nat) => IRList.cons IRMemSlot (IRMemSlot.mk b m Bool.true) (ih (Nat.add b ir_d8))) \
             ms a"
                .to_string(),
            "ir_vtable_method_cells a ms: the method slots of a vtable image, one live cell per \
             entry of `ms`, at byte offsets a, a+8, a+16, .. — one pointer-sized word per cell at \
             the 64-bit target the lane pins.",
        ),
        (
            "def ir_vtable_cells (vt : Nat) (drop : IRScalar) (size : Nat) (align : Nat) \
             (ms : IRList IRScalar) : IRList IRMemSlot := \
             IRList.cons IRMemSlot (IRMemSlot.mk vt drop Bool.true) \
             (IRList.cons IRMemSlot (IRMemSlot.mk (Nat.add vt ir_d8) (IRScalar.int_ size) Bool.true) \
             (IRList.cons IRMemSlot (IRMemSlot.mk (Nat.add vt ir_d16) (IRScalar.int_ align) Bool.true) \
             (ir_vtable_method_cells (Nat.add vt ir_d24) ms)))"
                .to_string(),
            "ir_vtable_cells vt drop size align ms: THE VTABLE IMAGE — the region rustc's \
             `tcx.vtable_allocation(source, principal)` lays out, `[drop_in_place, size, align, \
             methods..]` (COMMON_VTABLE_ENTRIES), as cells at vt, vt+8, vt+16, vt+24.. . The drop \
             slot is a function pointer, or null when the type has no drop glue; size and align \
             are integers; the methods are function pointers. A caller-supplied heap containing \
             this region is what D14's align read is exact over.",
        ),
    ]);
    for (name, off, what) in [
        ("ir_vtable_size_load", "ir_d8", "SIZE (slot 1, +8)"),
        ("ir_vtable_align_load", "ir_d16", "ALIGN (slot 2, +16)"),
    ] {
        let a = format!("(Nat.add vt {off})");
        let some =
            format!("(IROption.some IRMemSlot (IRMemSlot.mk {a} (IRScalar.int_ w) Bool.true))");
        out.push((
            format!(
                "def {name} (mem : IRList IRMemSlot) (vt : Nat) (w : Nat) \
                 (h : ir_vtable_slot mem {a} (IRScalar.int_ w)) : Eq IRStepResult \
                 (ir_load_at mem (IRScalar.ptr_ {a})) (IRStepResult.value (IRScalar.int_ w)) := \
                 Eq.subst (IROption IRMemSlot) (fun (o : IROption IRMemSlot) => Eq IRStepResult \
                 (ir_load_slot o) (IRStepResult.value (IRScalar.int_ w))) {some} \
                 (ir_mem_lookup mem {a}) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup mem {a}) \
                 {some} h) (Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ w)))"
            ),
            if what.starts_with("SIZE") {
                "ir_vtable_size_load: a load through vt+8 of a heap holding the vtable's SIZE word \
                 there returns that word. DerivedProved, zero axiom_deps."
            } else {
                "ir_vtable_align_load: D14's slot read, exact — a load through vt+16 of a heap \
                 holding the vtable's ALIGN word there returns that word, which is what the \
                 compiled program reads (`size_and_align_of_dst`). DerivedProved, zero axiom_deps."
            },
        ));
    }
    out.extend([
        (
            "def ir_vtable_slot_frame_store (mem : IRList IRMemSlot) (a : Nat) (x : Nat) \
             (v : IRScalar) (w : IRScalar) (hne : Eq Bool (ir_nat_eqb a x) Bool.false) \
             (h : ir_vtable_slot mem x w) : ir_vtable_slot (ir_mem_update mem a v) x w := \
             Eq.trans (IROption IRMemSlot) (ir_mem_lookup (ir_mem_update mem a v) x) \
             (ir_mem_lookup mem x) (IROption.some IRMemSlot (IRMemSlot.mk x w Bool.true)) \
             (ir_mem_lookup_update_skip mem a x v hne) h"
                .to_string(),
            "ir_vtable_slot_frame_store: the EvalIR half of READ-ONLY — a store to any address \
             other than the slot's leaves the slot's word as it was. The other half is the \
             projector's: it refuses a store, an escape or an uncertified load through a pointer \
             derived from a vtable word (crystal memo §23). DerivedProved, zero axiom_deps.",
        ),
        (
            "def ir_e5_d14_gep (vt : Nat) : Eq IRStepResult \
             (ir_gep_eval (IRScalar.ptr_ vt) (IRList.cons IRScalar (IRScalar.int_ ir_d16) \
             (IRList.nil IRScalar))) (IRStepResult.value (IRScalar.ptr_ (Nat.add vt ir_d16))) := \
             Eq.refl IRStepResult (IRStepResult.value (IRScalar.ptr_ (Nat.add vt ir_d16)))"
                .to_string(),
            "ir_e5_d14_gep: D14's `gep inbounds i8, ptr %vt, 16` addresses cell vt+16 — the \
             byte offset IS the cell offset, because the cell machine's GEP is single-scale \
             and D14 steps in i8. With ir_e5_ptrmeta_mt_is_read before it and \
             ir_vtable_align_load after it, that is the whole D14 read. DerivedProved, zero \
             axiom_deps.",
        ),
    ]);
    out
}

impl Specification {
    /// Register the E5 declarations, in [`E5_NAMES`] order.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or kernel-check.
    pub(super) fn add_eval_ir_e5(&mut self) -> Result<(), SpecError> {
        for (source, description) in decls() {
            self.add_recursive_def(&source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_e5_sources_are_ascii_balanced_and_named_in_order() {
        let ds = decls();
        assert_eq!(ds.len(), E5_NAMES.len());
        for ((src, _), name) in ds.iter().zip(E5_NAMES) {
            assert!(src.is_ascii(), "{name}: spec sources stay ASCII");
            assert_eq!(
                src.matches('(').count(),
                src.matches(')').count(),
                "{name}: unbalanced parentheses"
            );
            assert!(src.starts_with(&format!("def {name} ")), "{name}");
        }
    }

    /// The icmp rows are stated for BOTH operators at EVERY fat kind the cell
    /// machine admits, so a later arm that answered one of them would fail a
    /// named declaration rather than pass silently.
    #[test]
    fn test_e5_icmp_rows_cover_every_admitted_fat_kind() {
        for kind in ["containerlen", "containervtable", "fatdyn"] {
            for op in ["eq", "ne"] {
                let name = format!("ir_e5_icmp_{op}_{kind}_refused");
                assert!(E5_NAMES.contains(&name.as_str()), "{name} missing");
            }
        }
    }
}
