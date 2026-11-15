// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked byte-memory operations for the versioned 64-bit little-endian IR
//! profile. This is a distinct denotation, not a claim that the older cell
//! machine already models byte layouts or native pointer provenance.
//!
//! Memory is a persistent partial byte function. Accesses require one live
//! allocation containing the complete range; initialized bytes, exact scalar
//! encodings, requested alignment, and address bounds are checked separately.
//! Retiring an activation leaves the bytes observable in the final memory but
//! makes that activation's allocations inaccessible. None of these definitions
//! proves an allocator, external helper, machine ABI, or compiled executable.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    fn add_byte_memory_definition(
        &mut self,
        source: &str,
        description: &str,
    ) -> Result<(), SpecError> {
        let name = source
            .split_whitespace()
            .nth(1)
            .unwrap_or("<unnamed byte definition>");
        self.add_recursive_def(source, description)
            .map_err(|error| match error {
                SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
                SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                SpecError::EnvError(detail) => SpecError::EnvError(format!("{name}: {detail}")),
                // A declaration-budget failure already carries its exact root and
                // must remain a resource failure, not be relabeled a type error.
                other => other,
            })
    }

    pub(super) fn add_eval_ir_byte_memory(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_byte_memory_words()?;
        self.add_eval_ir_byte_memory_ranges()?;
        self.add_eval_ir_byte_memory_access()
    }

    fn add_eval_ir_byte_memory_words(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (r"def ir_byte_limit_v1 : Nat := 18446744073709551616",
             "Exclusive 64-bit byte-address limit; this profile is explicitly 64LE."),
            (r"def ir_byte_pow2_go_v1 (fuel : Nat) (n : Nat) : Bool :=
@Nat.rec (fun (_ : Nat) => Nat -> Bool)
  (fun (_ : Nat) => Bool.false)
  (fun (_ : Nat) (ih : Nat -> Bool) => fun (x : Nat) =>
    @Bool.rec (fun (_ : Bool) => Bool)
      (Bool.and (ir_nat_pos x) (Bool.and (ir_nat_eqb (Nat.mod x 2) 0) (ih (Nat.div x 2))))
      Bool.true (ir_nat_eqb x 1)) fuel n",
             "Bounded power-of-two alignment test. Each step halves its operand; no subtraction-loop division."),
            (r"def ir_byte_alignment_v1 (a : Nat) : Bool :=
Bool.and (ir_nat_ltb a ir_byte_limit_v1) (ir_byte_pow2_go_v1 64 a)",
             "Admitted explicit alignment: a nonzero 64-bit power of two."),
            (r"def ir_byte_in_range_v1 (base : Nat) (size : Nat) (address : Nat) : Bool :=
Bool.and (ir_nat_leb base address) (ir_nat_ltb address (Nat.add base size))",
             "Half-open byte extent membership using unbounded arithmetic before any address bound check."),
            (r"def ir_byte_clear_v1 (bytes : Nat -> IROption Nat) (base : Nat) (size : Nat) : Nat -> IROption Nat :=
fun (address : Nat) => @Bool.rec (fun (_ : Bool) => IROption Nat)
  (bytes address) (@IROption.none Nat) (ir_byte_in_range_v1 base size address)",
             "Fresh allocations are uninitialized even if an arbitrary incoming byte function had entries there."),
            (r"def ir_byte_read_word_v1 (bytes : Nat -> IROption Nat) (size : Nat) (base : Nat) : IROption Nat :=
@Nat.rec (fun (_ : Nat) => Nat -> IROption Nat)
  (fun (_ : Nat) => @IROption.some Nat 0)
  (fun (_ : Nat) (ih : Nat -> IROption Nat) => fun (address : Nat) =>
    @IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat)
      (@IROption.none Nat)
      (fun (byte : Nat) => @Bool.rec (fun (_ : Bool) => IROption Nat)
        (@IROption.none Nat)
        (@IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat)
          (@IROption.none Nat)
          (fun (rest : Nat) => @IROption.some Nat (Nat.add byte (Nat.mul 256 rest)))
          (ih (Nat.succ address)))
        (ir_nat_ltb byte 256))
      (bytes address)) size base",
             "Little-endian read; every byte must be initialized and below 256. Public accesses bound size to at most 16."),
            (r"def ir_byte_write_word_v1 (bytes : Nat -> IROption Nat) (base : Nat) (size : Nat) (word : Nat) : Nat -> IROption Nat :=
fun (address : Nat) => @Bool.rec (fun (_ : Bool) => IROption Nat)
  (bytes address)
  (@IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 (Nat.sub address base)))) 256))
  (ir_byte_in_range_v1 base size address)",
             "Persistent little-endian scalar store; addresses outside the exact stored range preserve the prior byte function."),
            (r"def ir_byte_pointer_address_v1 (value : IRScalar) : IROption Nat := match value with
| IRScalar.undef_ => @IROption.none Nat
| IRScalar.bool_ b => @IROption.none Nat
| IRScalar.int_ n => @IROption.none Nat
| IRScalar.float_ n => @IROption.none Nat
| IRScalar.unit_ => @IROption.none Nat
| IRScalar.ptr_ address => @Bool.rec (fun (_ : Bool) => IROption Nat) (@IROption.none Nat) (@IROption.some Nat address) (ir_nat_ltb address ir_byte_limit_v1)
| IRScalar.nullptr_ => @IROption.some Nat 0
| IRScalar.fat_ address metadata => @IROption.none Nat
| IRScalar.fnptr_ fid => @IROption.none Nat
| IRScalar.aggv fields => @IROption.none Nat
| IRScalar.vnil => @IROption.none Nat
| IRScalar.vcons value rest => @IROption.none Nat",
             "Thin data-pointer word only; integer and function carriers are not silently reinterpreted as data pointers."),
            (r"def ir_byte_pointer_value_v1 (address : Nat) : IRScalar :=
@Bool.rec (fun (_ : Bool) => IRScalar) (IRScalar.ptr_ address) IRScalar.nullptr_ (ir_nat_eqb address 0)",
             "The byte profile reserves the all-zero pointer representation for nullptr, unlike the legacy cell machine."),
        ] {
            self.add_byte_memory_definition(source, description)?;
        }
        Ok(())
    }

    fn add_eval_ir_byte_memory_ranges(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (r"def ir_byte_alloc_valid_v1 (a : IRByteAllocationV1) : Bool :=
Bool.and (ir_nat_pos (ir_byte_alloc_base_v1 a))
  (Bool.and (ir_nat_pos (ir_byte_alloc_size_v1 a))
    (ir_nat_leb (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) ir_byte_limit_v1))",
             "Valid nonempty allocation extent in the non-null 64-bit byte-address space."),
            (r"def ir_byte_overlaps_v1 (a : IRByteAllocationV1) (base : Nat) (size : Nat) : Bool :=
Bool.and (ir_nat_pos (ir_byte_alloc_size_v1 a))
  (Bool.and (ir_nat_pos size)
    (Bool.and (ir_nat_ltb (ir_byte_alloc_base_v1 a) (Nat.add base size))
      (ir_nat_ltb base (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)))))",
             "Half-open extent overlap, including retired allocations; retired addresses are never recycled by this profile."),
            (r"def ir_byte_overlap_count_v1 (allocs : IRList IRByteAllocationV1) (base : Nat) (size : Nat) : Nat :=
@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Nat)
  0
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Nat) =>
    @Bool.rec (fun (_ : Bool) => Nat) ih (Nat.succ ih) (ir_byte_overlaps_v1 a base size)) allocs",
             "Actual overlapping allocation count, not membership in an assumed well-formed allocation list."),
            (r"def ir_byte_cover_v1 (a : IRByteAllocationV1) (base : Nat) (size : Nat) : Bool :=
Bool.and (ir_byte_alloc_valid_v1 a)
  (Bool.and (ir_byte_alloc_live_v1 a)
    (Bool.and (ir_nat_leb (ir_byte_alloc_base_v1 a) base)
      (ir_nat_leb (Nat.add base size) (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)))))",
             "A live, valid allocation contains the complete requested byte extent."),
            (r"def ir_byte_any_cover_v1 (allocs : IRList IRByteAllocationV1) (base : Nat) (size : Nat) : Bool :=
@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Bool)
  Bool.false
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Bool) =>
    Bool.or (ir_byte_cover_v1 a base size) ih) allocs",
             "Lookup-based extent coverage: every memory access also checks uniqueness of all overlapping extents."),
            (r"def ir_byte_accessible_v1 (allocs : IRList IRByteAllocationV1) (base : Nat) (size : Nat) (align : Nat) : Bool :=
Bool.and (ir_nat_pos base)
  (Bool.and (ir_nat_pos size)
    (Bool.and (ir_nat_leb (Nat.add base size) ir_byte_limit_v1)
      (Bool.and (ir_byte_alignment_v1 align)
        (Bool.and (ir_nat_eqb (Nat.mod base align) 0)
          (Bool.and (ir_nat_eqb (ir_byte_overlap_count_v1 allocs base size) 1)
            (ir_byte_any_cover_v1 allocs base size))))))",
             "Bounds, promised alignment, unique allocation ownership, and liveness are jointly required; crossing adjacent allocations is not a valid load/store."),
            (r"def ir_byte_retire_allocs_v1 (owner : Nat) (allocs : IRList IRByteAllocationV1) : IRList IRByteAllocationV1 :=
@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => IRList IRByteAllocationV1)
  (@IRList.nil IRByteAllocationV1)
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : IRList IRByteAllocationV1) =>
    @IRList.cons IRByteAllocationV1
      (IRByteAllocationV1.mk (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a) (ir_byte_alloc_owner_v1 a)
        (Bool.and (ir_byte_alloc_live_v1 a) (Bool.not (ir_nat_eqb owner (ir_byte_alloc_owner_v1 a))))) ih) allocs",
             "Retire exactly the returning activation's allocations; caller-owned captured environments remain live."),
            (r"def ir_byte_retire_v1 (owner : Nat) (mem : IRByteMemoryV1) : IRByteMemoryV1 :=
IRByteMemoryV1.mk (ir_byte_retire_allocs_v1 owner (ir_byte_mem_allocs_v1 mem)) (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem)",
             "Activation retirement preserves the complete final byte map and address cursor, including on subsequent failure."),
            (r"def ir_byte_memory_empty_v1 (nextAddress : Nat) : IRByteMemoryV1 :=
IRByteMemoryV1.mk (@IRList.nil IRByteAllocationV1) (fun (_ : Nat) => @IROption.none Nat) nextAddress",
             "Empty memory with an explicit caller-supplied allocation cursor; allocation checks its range before use."),
            (r"def ir_byte_effective_align_v1 (requested : Nat) (natural : Nat) : Nat :=
@Bool.rec (fun (_ : Bool) => Nat) requested natural (ir_nat_eqb requested 0)",
             "Zero is the reflected absent-alignment sentinel and resolves to natural layout alignment. Explicit Some(0) must be rejected before reflection."),
            (r"def ir_byte_aligned_base_v1 (nextAddress : Nat) (align : Nat) : Nat :=
Nat.mul (Nat.div (Nat.add nextAddress (Nat.sub align 1)) align) align",
             "Round a checked cursor upward using exact Nat arithmetic, never wrapped machine addition."),
            (r"def ir_byte_allocate_range_v1 (size : Nat) (align : Nat) (owner : Nat) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
let base : Nat := ir_byte_aligned_base_v1 (ir_byte_mem_next_v1 mem) align;
let endAddress : Nat := Nat.add base size;
@Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
  (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) mem)
  (IRByteMemoryResultV1.value (IRScalar.ptr_ base)
    (IRByteMemoryV1.mk
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size owner Bool.true) (ir_byte_mem_allocs_v1 mem))
      (ir_byte_clear_v1 (ir_byte_mem_bytes_v1 mem) base size) (Nat.succ endAddress)))
  (Bool.and (ir_nat_pos (ir_byte_mem_next_v1 mem))
    (Bool.and (ir_nat_ltb (ir_byte_mem_next_v1 mem) ir_byte_limit_v1)
      (Bool.and (ir_nat_pos size)
        (Bool.and (ir_byte_alignment_v1 align)
          (Bool.and (ir_nat_pos base)
            (Bool.and (ir_nat_ltb endAddress ir_byte_limit_v1)
              (ir_nat_eqb (ir_byte_overlap_count_v1 (ir_byte_mem_allocs_v1 mem) base size) 0)))))))",
             "Fresh aligned nonempty extent, checked before publication. A one-byte guard gap separates new allocations and their one-past pointers; no address is reused."),
            (r"def ir_byte_alloc_v1 (ctx : IRByteContextV1) (ty : IRTy) (count : Nat) (align : Nat) (owner : Nat) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
@IROption.rec IRByteLayoutV1 (fun (_ : IROption IRByteLayoutV1) => IRByteMemoryResultV1)
  (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
  (fun (layout : IRByteLayoutV1) => @Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
    (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
    (ir_byte_allocate_range_v1 (Nat.mul (ir_byte_layout_size_v1 layout) count)
      (ir_byte_effective_align_v1 align (ir_byte_layout_align_v1 layout)) owner mem)
    (Bool.and (ir_nat_pos count)
      (Bool.and (ir_nat_pos (ir_byte_layout_size_v1 layout))
        (Bool.and (ir_nat_ltb count ir_byte_limit_v1)
          (Bool.and (ir_nat_ltb (ir_byte_layout_size_v1 layout) ir_byte_limit_v1)
            (ir_byte_alignment_v1 (ir_byte_layout_align_v1 layout)))))))
  (ir_byte_layout_v1 ctx ty)",
             "Typed allocation uses the actual reflected pointee layout and count, including array extent; it does not allocate one untyped scalar cell."),
        ] {
            self.add_byte_memory_definition(source, description)?;
        }
        Ok(())
    }

    fn add_eval_ir_byte_memory_access(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (r"def ir_byte_integer_size_v1 (width : Nat) : IROption Nat :=
@Bool.rec (fun (_ : Bool) => IROption Nat) (@IROption.none Nat) (@IROption.some Nat (Nat.div width 8))
  (Bool.or (ir_nat_eqb width 8) (Bool.or (ir_nat_eqb width 16)
    (Bool.or (ir_nat_eqb width 32) (Bool.or (ir_nat_eqb width 64) (ir_nat_eqb width 128)))))",
             "The exact admitted integer memory widths, not an arbitrary size supplied by the producer."),
            (r"def ir_byte_lane_size_v1 (ty : IRTy) : IROption Nat := match ty with
| IRTy.bool_ => @IROption.some Nat 1
| IRTy.int_ width => ir_byte_integer_size_v1 width
| IRTy.uint_ width => ir_byte_integer_size_v1 width
| IRTy.float_ width => @IROption.none Nat
| IRTy.ptr_ => @IROption.some Nat 8
| IRTy.ref_ inner => @IROption.some Nat 8
| IRTy.refmut_ inner => @IROption.some Nat 8
| IRTy.rawconst_ inner => @IROption.some Nat 8
| IRTy.rawmut_ inner => @IROption.some Nat 8
| IRTy.rc_ inner => @IROption.some Nat 8
| IRTy.fatptr_ inner => @IROption.none Nat
| IRTy.unit_ => @IROption.none Nat
| IRTy.never_ => @IROption.none Nat
| IRTy.tuple_ id => @IROption.none Nat
| IRTy.array_ inner count => @IROption.none Nat
| IRTy.struct_ id => @IROption.none Nat
| IRTy.enum_ id => @IROption.none Nat
| IRTy.func_ id => @IROption.some Nat 8
| IRTy.usize_ bits => @Bool.rec (fun (_ : Bool) => IROption Nat) (@IROption.none Nat) (@IROption.some Nat 8) (ir_nat_eqb bits 64)
| IRTy.fatstr_ => @IROption.none Nat
| IRTy.fatslice_ element => @IROption.none Nat
| IRTy.fatdyn_ traitId => @IROption.none Nat
| IRTy.containerlen_ => @IROption.none Nat
| IRTy.containervtable_ => @IROption.none Nat",
             "Only integer, Boolean, thin pointer, and exact function-pointer scalar memory is admitted. Arrays have allocation layouts, not invented aggregate load/store semantics."),
            (r"def ir_byte_function_word_v1 (ctx : IRByteContextV1) (fid : Nat) : IROption Nat :=
@IROption.rec IRByteFunctionV1 (fun (_ : IROption IRByteFunctionV1) => IROption Nat)
  (@IROption.none Nat)
  (fun (binding : IRByteFunctionV1) =>
    @IROption.rec IRByteFunctionV1 (fun (_ : IROption IRByteFunctionV1) => IROption Nat)
      (@IROption.none Nat)
      (fun (reverse : IRByteFunctionV1) => @Bool.rec (fun (_ : Bool) => IROption Nat)
        (@IROption.none Nat) (@IROption.some Nat (ir_byte_binding_address_v1 binding))
        (Bool.and (ir_nat_eqb (ir_byte_binding_fid_v1 binding) fid)
          (Bool.and (ir_nat_eqb (ir_byte_binding_fid_v1 reverse) fid)
            (Bool.and (ir_nat_eqb (ir_byte_binding_sig_v1 reverse) (ir_byte_binding_sig_v1 binding))
              (Bool.and (ir_nat_eqb (ir_byte_binding_address_v1 reverse) (ir_byte_binding_address_v1 binding))
                (Bool.and (ir_nat_pos (ir_byte_binding_address_v1 binding))
                  (ir_nat_ltb (ir_byte_binding_address_v1 binding) ir_byte_limit_v1)))))))
      (ir_byte_function_address_v1 ctx (ir_byte_binding_address_v1 binding)))
  (ir_byte_function_v1 ctx fid)",
             "Encode an exact function identity through the checked ID/address catalog in both directions; no name alias or host override is consulted."),
            (r"def ir_byte_decode_function_v1 (ctx : IRByteContextV1) (sig : Nat) (word : Nat) : IROption IRScalar :=
@IROption.rec IRByteFunctionV1 (fun (_ : IROption IRByteFunctionV1) => IROption IRScalar)
  (@IROption.none IRScalar)
  (fun (binding : IRByteFunctionV1) =>
    @IROption.rec Nat (fun (_ : IROption Nat) => IROption IRScalar)
      (@IROption.none IRScalar)
      (fun (address : Nat) => @Bool.rec (fun (_ : Bool) => IROption IRScalar)
        (@IROption.none IRScalar) (@IROption.some IRScalar (IRScalar.fnptr_ (ir_byte_binding_fid_v1 binding)))
        (Bool.and (ir_nat_eqb address word) (ir_nat_eqb sig (ir_byte_binding_sig_v1 binding))))
      (ir_byte_function_word_v1 ctx (ir_byte_binding_fid_v1 binding)))
  (ir_byte_function_address_v1 ctx word)",
             "Typed function-pointer decoding checks the actual byte word, exact function identity, and requested signature before constructing a callable scalar."),
            (r"def ir_byte_scalar_word_v1 (ctx : IRByteContextV1) (value : IRScalar) : IROption Nat := match value with
| IRScalar.undef_ => @IROption.none Nat
| IRScalar.bool_ b => @IROption.some Nat (@Bool.rec (fun (_ : Bool) => Nat) 0 1 b)
| IRScalar.int_ n => @IROption.some Nat n
| IRScalar.float_ n => @IROption.none Nat
| IRScalar.unit_ => @IROption.none Nat
| IRScalar.ptr_ address => @Bool.rec (fun (_ : Bool) => IROption Nat) (@IROption.none Nat) (@IROption.some Nat address) (Bool.and (ir_nat_pos address) (ir_nat_ltb address ir_byte_limit_v1))
| IRScalar.nullptr_ => @IROption.some Nat 0
| IRScalar.fat_ address metadata => @IROption.none Nat
| IRScalar.fnptr_ fid => ir_byte_function_word_v1 ctx fid
| IRScalar.aggv fields => @IROption.none Nat
| IRScalar.vnil => @IROption.none Nat
| IRScalar.vcons value rest => @IROption.none Nat",
             "Canonical scalar representation. Signed integers retain their Nat bit-pattern carrier; no sign or tag bits are changed."),
            (r"def ir_byte_decode_word_v1 (ctx : IRByteContextV1) (ty : IRTy) (word : Nat) : IROption IRScalar := match ty with
| IRTy.bool_ => @Bool.rec (fun (_ : Bool) => IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar (IRScalar.bool_ (ir_nat_eqb word 1))) (ir_nat_ltb word 2)
| IRTy.int_ width => @IROption.some IRScalar (IRScalar.int_ word)
| IRTy.uint_ width => @IROption.some IRScalar (IRScalar.int_ word)
| IRTy.float_ width => @IROption.none IRScalar
| IRTy.ptr_ => @IROption.some IRScalar (ir_byte_pointer_value_v1 word)
| IRTy.ref_ inner => @IROption.some IRScalar (ir_byte_pointer_value_v1 word)
| IRTy.refmut_ inner => @IROption.some IRScalar (ir_byte_pointer_value_v1 word)
| IRTy.rawconst_ inner => @IROption.some IRScalar (ir_byte_pointer_value_v1 word)
| IRTy.rawmut_ inner => @IROption.some IRScalar (ir_byte_pointer_value_v1 word)
| IRTy.rc_ inner => @IROption.some IRScalar (ir_byte_pointer_value_v1 word)
| IRTy.fatptr_ inner => @IROption.none IRScalar
| IRTy.unit_ => @IROption.none IRScalar
| IRTy.never_ => @IROption.none IRScalar
| IRTy.tuple_ id => @IROption.none IRScalar
| IRTy.array_ inner count => @IROption.none IRScalar
| IRTy.struct_ id => @IROption.none IRScalar
| IRTy.enum_ id => @IROption.none IRScalar
| IRTy.func_ sig => ir_byte_decode_function_v1 ctx sig word
| IRTy.usize_ bits => @Bool.rec (fun (_ : Bool) => IROption IRScalar) (@IROption.none IRScalar) (@IROption.some IRScalar (IRScalar.int_ word)) (ir_nat_eqb bits 64)
| IRTy.fatstr_ => @IROption.none IRScalar
| IRTy.fatslice_ element => @IROption.none IRScalar
| IRTy.fatdyn_ traitId => @IROption.none IRScalar
| IRTy.containerlen_ => @IROption.none IRScalar
| IRTy.containervtable_ => @IROption.none IRScalar",
             "Scalar decoding follows the actual requested type. Public loads separately check lane width and the canonical typed-value predicate."),
            (r"def ir_byte_load_at_v1 (ctx : IRByteContextV1) (ty : IRTy) (address : Nat) (size : Nat) (align : Nat) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
@Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
  (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) mem)
  (@IROption.rec Nat (fun (_ : IROption Nat) => IRByteMemoryResultV1)
    (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.uninit) mem)
    (fun (word : Nat) =>
      @IROption.rec IRScalar (fun (_ : IROption IRScalar) => IRByteMemoryResultV1)
        (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.width_bounded) mem)
        (fun (value : IRScalar) => @Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
          (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.width_bounded) mem)
          (IRByteMemoryResultV1.value value mem) (ir_byte_value_matches_v1 ctx ty value))
        (ir_byte_decode_word_v1 ctx ty word))
    (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) size address))
  (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address size align)",
             "Initialized typed scalar load, with original memory retained on all administrative faults."),
            (r"def ir_byte_store_at_v1 (ctx : IRByteContextV1) (ty : IRTy) (address : Nat) (value : IRScalar) (size : Nat) (align : Nat) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
@Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
  (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) mem)
  (@Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
    (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.width_bounded) mem)
    (@IROption.rec Nat (fun (_ : IROption Nat) => IRByteMemoryResultV1)
      (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.width_bounded) mem)
      (fun (word : Nat) => @Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
        (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.width_bounded) mem)
        (IRByteMemoryResultV1.value IRScalar.unit_
          (IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 mem)
            (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) address size word) (ir_byte_mem_next_v1 mem)))
        (ir_nat_ltb word (ir_nat_pow2 (Nat.mul 8 size))))
      (ir_byte_scalar_word_v1 ctx value))
    (ir_byte_value_matches_v1 ctx ty value))
  (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address size align)",
             "Typed scalar store changes exactly its byte extent after all checks pass; it never silently wraps an out-of-range integer or function address."),
        ] {
            self.add_byte_memory_definition(source, description)?;
        }
        self.add_eval_ir_byte_memory_dispatch()
    }

    fn add_eval_ir_byte_memory_dispatch(&mut self) -> Result<(), SpecError> {
        // The shared layout/representation checks are generated once for each
        // public operation; the checked definitions, not this Rust source
        // generator, supply the eventual memory denotation.
        for (name, value_parameter, operation) in [
            ("load", "", "ir_byte_load_at_v1 ctx ty address size (ir_byte_effective_align_v1 align (ir_byte_layout_align_v1 layout)) mem"),
            ("store", " (value : IRScalar)", "ir_byte_store_at_v1 ctx ty address value size (ir_byte_effective_align_v1 align (ir_byte_layout_align_v1 layout)) mem"),
        ] {
            let source = format!(r"def ir_byte_{name}_v1 (ctx : IRByteContextV1) (ty : IRTy) (ptr : IRScalar){value_parameter} (align : Nat) (volatile : Bool) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
@Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
  (@IROption.rec Nat (fun (_ : IROption Nat) => IRByteMemoryResultV1)
    (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
    (fun (size : Nat) =>
      @IROption.rec IRByteLayoutV1 (fun (_ : IROption IRByteLayoutV1) => IRByteMemoryResultV1)
        (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
        (fun (layout : IRByteLayoutV1) => @Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
          (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.width_bounded) mem)
          (@IROption.rec Nat (fun (_ : IROption Nat) => IRByteMemoryResultV1)
            (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.not_ptr) mem)
            (fun (address : Nat) => {operation}) (ir_byte_pointer_address_v1 ptr))
          (Bool.and (ir_nat_eqb size (ir_byte_layout_size_v1 layout))
            (ir_byte_alignment_v1 (ir_byte_layout_align_v1 layout))))
        (ir_byte_layout_v1 ctx ty))
    (ir_byte_lane_size_v1 ty))
  (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem) volatile");
            self.add_byte_memory_definition(
                &source,
                "Versioned nonvolatile scalar byte access: exact type/layout, natural-or-explicit alignment, canonical values, complete live extent, and initialized bytes. Volatile accesses are explicitly outside this profile.",
            )?;
        }
        self.add_eval_ir_byte_memory_gep()
    }

    fn add_eval_ir_byte_memory_gep(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (r"def ir_byte_gep_index_v1 (value : IRScalar) : IROption Nat := match value with
| IRScalar.undef_ => @IROption.none Nat
| IRScalar.bool_ b => @IROption.none Nat
| IRScalar.int_ n => @Bool.rec (fun (_ : Bool) => IROption Nat) (@IROption.none Nat) (@IROption.some Nat n) (ir_nat_ltb n 9223372036854775808)
| IRScalar.float_ n => @IROption.none Nat
| IRScalar.unit_ => @IROption.none Nat
| IRScalar.ptr_ address => @IROption.none Nat
| IRScalar.nullptr_ => @IROption.none Nat
| IRScalar.fat_ address metadata => @IROption.none Nat
| IRScalar.fnptr_ fid => @IROption.none Nat
| IRScalar.aggv fields => @IROption.none Nat
| IRScalar.vnil => @IROption.none Nat
| IRScalar.vcons value rest => @IROption.none Nat",
             "The v1 GEP profile admits canonical nonnegative signed-64 indices only. Exact module reflection must check the actual SSA index type; erased Nat carriers cannot distinguish signed from unsigned operands."),
            (r"def ir_byte_gep_indices_v1 (indices : IRList IRScalar) : IROption Nat :=
@IRList.rec IRScalar (fun (_ : IRList IRScalar) => IROption Nat)
  (@IROption.some Nat 0)
  (fun (value : IRScalar) (_ : IRList IRScalar) (ih : IROption Nat) =>
    @IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat)
      (@IROption.none Nat)
      (fun (index : Nat) =>
        @IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat)
          (@IROption.none Nat)
          (fun (rest : Nat) => @Bool.rec (fun (_ : Bool) => IROption Nat)
            (@IROption.none Nat) (@IROption.some Nat (Nat.add index rest))
            (ir_nat_ltb (Nat.add index rest) ir_byte_limit_v1)) ih)
      (ir_byte_gep_index_v1 value)) indices",
             "Checked sum of the admitted GEP indices. TrustIR strides each index by the same pointee byte size; this is not LLVM aggregate-index traversal."),
            (r"def ir_byte_point_count_v1 (allocs : IRList IRByteAllocationV1) (address : Nat) : Nat :=
@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Nat)
  0
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Nat) =>
    @Bool.rec (fun (_ : Bool) => Nat) ih (Nat.succ ih)
      (Bool.and (ir_nat_leb (ir_byte_alloc_base_v1 a) address)
        (ir_nat_leb address (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a))))) allocs",
             "Closed-extent point count for inbounds GEP, including one-past pointers and malformed overlapping allocation records."),
            (r"def ir_byte_same_allocation_v1 (allocs : IRList IRByteAllocationV1) (base : Nat) (result : Nat) : Bool :=
Bool.and (ir_nat_eqb (ir_byte_point_count_v1 allocs base) 1)
  (Bool.and (ir_nat_eqb (ir_byte_point_count_v1 allocs result) 1)
    (@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Bool)
      Bool.false
      (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Bool) =>
        Bool.or (Bool.and (ir_byte_cover_v1 a base 0) (ir_byte_cover_v1 a result 0)) ih) allocs))",
             "Inbounds pointers belong to the same unique live allocation; one-past is allowed but does not authorize a load/store."),
            (r"def ir_byte_gep_at_v1 (base : Nat) (stride : Nat) (index : Nat) (inbounds : Bool) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
let delta : Nat := Nat.mul stride index;
let result : Nat := Nat.add base delta;
@Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
  (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) mem)
  (IRByteMemoryResultV1.value (ir_byte_pointer_value_v1 result) mem)
  (Bool.and (ir_nat_pos base)
    (Bool.and (ir_nat_ltb delta ir_byte_limit_v1)
      (Bool.and (ir_nat_ltb result ir_byte_limit_v1)
        (Bool.or (Bool.not inbounds) (ir_byte_same_allocation_v1 (ir_byte_mem_allocs_v1 mem) base result)))))",
             "Nonwrapping byte pointer arithmetic. The inbounds flag adds same-live-allocation confinement; an ordinary GEP does not itself dereference memory."),
            (r"def ir_byte_gep_v1 (ctx : IRByteContextV1) (pointeeTy : IRTy) (base : IRScalar) (indices : IRList IRScalar) (inbounds : Bool) (mem : IRByteMemoryV1) : IRByteMemoryResultV1 :=
@IROption.rec IRByteLayoutV1 (fun (_ : IROption IRByteLayoutV1) => IRByteMemoryResultV1)
  (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
  (fun (layout : IRByteLayoutV1) => @Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1)
    (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
    (@IROption.rec Nat (fun (_ : IROption Nat) => IRByteMemoryResultV1)
      (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)
      (fun (index : Nat) =>
        @IROption.rec Nat (fun (_ : IROption Nat) => IRByteMemoryResultV1)
          (IRByteMemoryResultV1.fault (IROutcome.type_error IRFault.not_ptr) mem)
          (fun (address : Nat) => ir_byte_gep_at_v1 address (ir_byte_layout_size_v1 layout) index inbounds mem)
          (ir_byte_pointer_address_v1 base))
      (ir_byte_gep_indices_v1 indices))
    (Bool.and (ir_nat_pos (ir_byte_layout_size_v1 layout))
      (ir_nat_ltb (ir_byte_layout_size_v1 layout) ir_byte_limit_v1)))
  (ir_byte_layout_v1 ctx pointeeTy)",
             "Versioned typed GEP with exact pointee byte layout, admitted signed64 index list, checked sum/stride/address arithmetic, and actual inbounds flag."),
        ] {
            self.add_byte_memory_definition(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn checked(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
        spec.add_recursive_def(
            &format!("def {name} : @Eq ({ty}) ({actual}) ({expected}) := @Eq.refl ({ty}) ({expected})"),
            "Concrete byte-profile kernel-computation witness, not native/runtime implementation evidence.",
        ).expect("byte witness must elaborate and kernel-check");
        spec.verify_definition(name)
            .expect("independent kernel replay");
        assert!(spec
            .env()
            .axiom_deps(&Name::from_string(name))
            .expect("witness exists")
            .is_empty());
        assert!(spec
            .env()
            .trust_marker_deps(&Name::from_string(name))
            .expect("witness exists")
            .is_empty());
    }

    fn memory_spec() -> Specification {
        let mut spec = Specification::new_eval_ir_prelude_spec().expect("existing IR prelude");
        spec.add_eval_ir_byte_types().expect("checked byte types");
        spec.add_eval_ir_byte_memory().expect("checked byte memory");
        let nil = "@IRList.nil IRTy";
        let mut layouts = "@IRList.nil IRByteLayoutV1".to_owned();
        for (ty, size, align) in [
            ("IRTy.bool_", 1, 1),
            ("IRTy.int_ 8", 1, 1),
            ("IRTy.uint_ 8", 1, 1),
            ("IRTy.int_ 64", 8, 8),
            ("IRTy.uint_ 64", 8, 8),
            ("IRTy.int_ 128", 16, 16),
            ("IRTy.ptr_", 8, 8),
            ("IRTy.func_ 7", 8, 8),
            ("IRTy.func_ 8", 8, 8),
            ("IRTy.array_ (IRTy.int_ 8) 32", 32, 1),
        ] {
            layouts = format!("@IRList.cons IRByteLayoutV1 (IRByteLayoutV1.mk ({ty}) {size} {align} ({nil}) (@IRList.nil Nat)) ({layouts})");
        }
        let context = format!("def byte_test_ctx : IRByteContextV1 := IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal)) ({layouts}) (@IRList.cons IRByteSignatureV1 (IRByteSignatureV1.mk 7 ({nil}) ({nil}) Bool.false) (@IRList.cons IRByteSignatureV1 (IRByteSignatureV1.mk 8 ({nil}) ({nil}) Bool.false) (@IRList.nil IRByteSignatureV1))) (@IRList.cons IRByteFunctionV1 (IRByteFunctionV1.mk 17 7 4096 0 Bool.false) (@IRList.cons IRByteFunctionV1 (IRByteFunctionV1.mk 19 8 8192 0 Bool.false) (@IRList.nil IRByteFunctionV1))) (@IRList.nil IRByteSiteV1)");
        spec.add_recursive_def(
            &context,
            "Explicit test catalog; no native address authority",
        )
        .expect("test context");
        for source in [
            "def byte_test_mem : IRByteMemoryV1 := IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 32 1 Bool.true) (@IRList.nil IRByteAllocationV1)) (fun (_ : Nat) => @IROption.none Nat) 64",
            "def byte_test_after (r : IRByteMemoryResultV1) : IRByteMemoryV1 := match r with\n| IRByteMemoryResultV1.value v mem => mem\n| IRByteMemoryResultV1.fault outcome mem => mem",
            "def byte_test_outcome (r : IRByteMemoryResultV1) : IROutcome := match r with\n| IRByteMemoryResultV1.value v mem => IROutcome.ret (@IRList.cons IRScalar v (@IRList.nil IRScalar))\n| IRByteMemoryResultV1.fault outcome mem => outcome",
        ] {
            spec.add_recursive_def(source, "Byte-memory test fixture").expect("test helper");
        }
        spec
    }

    fn ret(value: &str) -> String {
        format!("IROutcome.ret (@IRList.cons IRScalar ({value}) (@IRList.nil IRScalar))")
    }

    #[test]
    fn scalar_bytes_preserve_high_bits_overlap_and_alignment() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = memory_spec();
            let store = "byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 16) (IRScalar.int_ 18446744073709551615) 0 Bool.false byte_test_mem)";
            checked(&mut spec, "byte_high_bits", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.uint_ 64) (IRScalar.ptr_ 16) 0 Bool.false ({store}))"),
                &ret("IRScalar.int_ 18446744073709551615"));
            let overlap = format!("byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.uint_ 8) (IRScalar.ptr_ 17) (IRScalar.int_ 0) 0 Bool.false ({store}))");
            checked(&mut spec, "byte_partial_alias", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.uint_ 64) (IRScalar.ptr_ 16) 0 Bool.false ({overlap}))"),
                &ret("IRScalar.int_ 18446744073709486335"));
            checked(&mut spec, "byte_uninitialized", "IROutcome",
                "byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 16) 0 Bool.false byte_test_mem)",
                "IROutcome.ub IRFault.uninit");
            checked(&mut spec, "byte_natural_alignment", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 17) 0 Bool.false ({store}))"),
                "IROutcome.ub IRFault.bad_addr");
            let unaligned = "byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 17) (IRScalar.int_ 9) 1 Bool.false byte_test_mem)";
            checked(&mut spec, "byte_explicit_unaligned", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 17) 1 Bool.false ({unaligned}))"), &ret("IRScalar.int_ 9"));
            checked(&mut spec, "byte_invalid_alignment", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 16) 3 Bool.false ({store}))"), "IROutcome.ub IRFault.bad_addr");
            let wide = "byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.int_ 128) (IRScalar.ptr_ 16) (IRScalar.int_ 340282366920938463463374607431768211455) 0 Bool.false byte_test_mem)";
            checked(&mut spec, "byte_wide_128", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 128) (IRScalar.ptr_ 16) 0 Bool.false ({wide}))"), &ret("IRScalar.int_ 340282366920938463463374607431768211455"));
        });
    }

    #[test]
    fn typed_function_addresses_and_invalid_bool_bytes_fail_closed() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = memory_spec();
            let function = "byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.func_ 7) (IRScalar.ptr_ 16) (IRScalar.fnptr_ 17) 0 Bool.false byte_test_mem)";
            checked(&mut spec, "byte_function_roundtrip", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.func_ 7) (IRScalar.ptr_ 16) 0 Bool.false ({function}))"), &ret("IRScalar.fnptr_ 17"));
            checked(&mut spec, "byte_wrong_function_signature", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.func_ 8) (IRScalar.ptr_ 16) 0 Bool.false ({function}))"), "IROutcome.ub IRFault.width_bounded");
            checked(&mut spec, "byte_wrong_function_store", "IROutcome",
                "byte_test_outcome (ir_byte_store_v1 byte_test_ctx (IRTy.func_ 7) (IRScalar.ptr_ 16) (IRScalar.fnptr_ 19) 0 Bool.false byte_test_mem)", "IROutcome.type_error IRFault.width_bounded");
            let invalid_bool = "byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.uint_ 8) (IRScalar.ptr_ 16) (IRScalar.int_ 2) 0 Bool.false byte_test_mem)";
            checked(&mut spec, "byte_bool_junk", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx IRTy.bool_ (IRScalar.ptr_ 16) 0 Bool.false ({invalid_bool}))"), "IROutcome.ub IRFault.width_bounded");
            checked(&mut spec, "byte_pointer_zero_not_canonical", "IROutcome",
                "byte_test_outcome (ir_byte_store_v1 byte_test_ctx IRTy.ptr_ (IRScalar.ptr_ 16) (IRScalar.ptr_ 0) 0 Bool.false byte_test_mem)", "IROutcome.type_error IRFault.width_bounded");
        });
    }

    #[test]
    fn allocation_extent_initialization_and_activation_retirement_are_observed() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = memory_spec();
            let allocation =
                "ir_byte_alloc_v1 byte_test_ctx (IRTy.array_ (IRTy.int_ 8) 32) 2 0 9 byte_test_mem";
            checked(
                &mut spec,
                "byte_array_allocation",
                "IROutcome",
                &format!("byte_test_outcome ({allocation})"),
                &ret("IRScalar.ptr_ 64"),
            );
            checked(
                &mut spec,
                "byte_array_extent",
                "Nat",
                &format!("ir_byte_mem_next_v1 (byte_test_after ({allocation}))"),
                "129",
            );
            let stored = format!("byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 64) (IRScalar.int_ 31) 0 Bool.false (byte_test_after ({allocation})))");
            checked(&mut spec, "byte_retire_preserves_caller", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 64) 0 Bool.false (ir_byte_retire_v1 8 ({stored})))"), &ret("IRScalar.int_ 31"));
            checked(&mut spec, "byte_retire_dead", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 64) 0 Bool.false (ir_byte_retire_v1 9 ({stored})))"), "IROutcome.ub IRFault.bad_addr");
            checked(
                &mut spec,
                "byte_retire_retains_final_bytes",
                "IROption Nat",
                &format!("ir_byte_mem_bytes_v1 (ir_byte_retire_v1 9 ({stored})) 64"),
                "@IROption.some Nat 31",
            );
            checked(&mut spec, "byte_one_past_gep", "IROutcome",
                "byte_test_outcome (ir_byte_gep_v1 byte_test_ctx (IRTy.int_ 8) (IRScalar.ptr_ 16) (@IRList.cons IRScalar (IRScalar.int_ 32) (@IRList.nil IRScalar)) Bool.true byte_test_mem)", &ret("IRScalar.ptr_ 48"));
            checked(&mut spec, "byte_one_past_not_dereferenceable", "IROutcome",
                "byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 8) (IRScalar.ptr_ 48) 0 Bool.false byte_test_mem)", "IROutcome.ub IRFault.bad_addr");
            checked(&mut spec, "byte_escape_inbounds", "IROutcome",
                "byte_test_outcome (ir_byte_gep_v1 byte_test_ctx (IRTy.int_ 8) (IRScalar.ptr_ 16) (@IRList.cons IRScalar (IRScalar.int_ 33) (@IRList.nil IRScalar)) Bool.true byte_test_mem)", "IROutcome.ub IRFault.bad_addr");
            checked(&mut spec, "byte_no_wrap", "IROutcome",
                "byte_test_outcome (ir_byte_gep_v1 byte_test_ctx (IRTy.int_ 8) (IRScalar.ptr_ 18446744073709551615) (@IRList.cons IRScalar (IRScalar.int_ 1) (@IRList.nil IRScalar)) Bool.false byte_test_mem)", "IROutcome.ub IRFault.bad_addr");
            checked(&mut spec, "byte_negative_outside_profile", "IROutcome",
                "byte_test_outcome (ir_byte_gep_v1 byte_test_ctx (IRTy.int_ 8) (IRScalar.ptr_ 16) (@IRList.cons IRScalar (IRScalar.int_ 18446744073709551615) (@IRList.nil IRScalar)) Bool.false byte_test_mem)", "IROutcome.unmodelled IRFault.width_bounded");
        });
    }

    #[test]
    fn allocation_and_access_reject_adversarial_memory_without_losing_the_world() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = memory_spec();
            let prefilled = "IRByteMemoryV1.mk (@IRList.nil IRByteAllocationV1) (fun (_ : Nat) => @IROption.some Nat 5) 64";
            let allocated = format!("byte_test_after (ir_byte_alloc_v1 byte_test_ctx (IRTy.int_ 64) 1 0 9 ({prefilled}))");
            checked(
                &mut spec,
                "byte_fresh_clears_stale_bytes",
                "IROption Nat",
                &format!("ir_byte_mem_bytes_v1 ({allocated}) 64"),
                "@IROption.none Nat",
            );
            checked(
                &mut spec,
                "byte_fresh_preserves_unrelated_bytes",
                "IROption Nat",
                &format!("ir_byte_mem_bytes_v1 ({allocated}) 63"),
                "@IROption.some Nat 5",
            );
            checked(&mut spec, "byte_fresh_uninitialized_read", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 64) 0 Bool.false ({allocated}))"),
                "IROutcome.ub IRFault.uninit");
            let retired = "IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 9 Bool.false) (@IRList.nil IRByteAllocationV1)) (fun (_ : Nat) => @IROption.some Nat 5) 64";
            checked(&mut spec, "byte_retired_address_not_reused", "IROutcome",
                &format!("byte_test_outcome (ir_byte_alloc_v1 byte_test_ctx (IRTy.int_ 64) 1 0 10 ({retired}))"),
                "IROutcome.ub IRFault.bad_addr");
            checked(&mut spec, "byte_failed_allocation_preserves_memory", "IRByteMemoryV1",
                &format!("byte_test_after (ir_byte_alloc_v1 byte_test_ctx (IRTy.int_ 64) 1 0 10 ({retired}))"), retired);
            let neighboring = "IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 4 1 Bool.true) (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 20 4 2 Bool.true) (@IRList.nil IRByteAllocationV1))) (fun (_ : Nat) => @IROption.some Nat 0) 64";
            checked(&mut spec, "byte_no_cross_allocation_read", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 16) 0 Bool.false ({neighboring}))"),
                "IROutcome.ub IRFault.bad_addr");
            let overlapping = "IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 16 1 Bool.true) (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 20 4 2 Bool.false) (@IRList.nil IRByteAllocationV1))) (fun (_ : Nat) => @IROption.some Nat 0) 64";
            checked(&mut spec, "byte_duplicate_extent_is_not_hidden", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 16) 0 Bool.false ({overlapping}))"),
                "IROutcome.ub IRFault.bad_addr");
            let stored = "byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 16) (IRScalar.int_ 31) 0 Bool.false byte_test_mem)";
            checked(&mut spec, "byte_failed_store_preserves_memory", "IRByteMemoryV1",
                &format!("byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.int_ 64) (IRScalar.ptr_ 17) (IRScalar.int_ 99) 0 Bool.false ({stored}))"), stored);
            checked(&mut spec, "byte_alloc_product_does_not_wrap", "IROutcome",
                "byte_test_outcome (ir_byte_alloc_v1 byte_test_ctx (IRTy.int_ 64) 18446744073709551615 0 9 byte_test_mem)",
                "IROutcome.ub IRFault.bad_addr");
            checked(&mut spec, "byte_zero_alloc_is_explicit_refusal", "IROutcome",
                "byte_test_outcome (ir_byte_alloc_v1 byte_test_ctx (IRTy.int_ 64) 0 0 9 byte_test_mem)",
                "IROutcome.unmodelled IRFault.width_bounded");
            let malformed = "IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 byte_test_mem) (fun (_ : Nat) => @IROption.some Nat 256) 64";
            checked(&mut spec, "byte_out_of_range_byte_not_truncated", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.uint_ 8) (IRScalar.ptr_ 16) 0 Bool.false ({malformed}))"),
                "IROutcome.ub IRFault.uninit");
            let nonexistent = "byte_test_after (ir_byte_store_v1 byte_test_ctx (IRTy.uint_ 64) (IRScalar.ptr_ 16) (IRScalar.int_ 4097) 0 Bool.false byte_test_mem)";
            checked(&mut spec, "byte_non_entry_function_address_refused", "IROutcome",
                &format!("byte_test_outcome (ir_byte_load_v1 byte_test_ctx (IRTy.func_ 7) (IRScalar.ptr_ 16) 0 Bool.false ({nonexistent}))"),
                "IROutcome.ub IRFault.width_bounded");
        });
    }
}
