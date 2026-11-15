// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conditional elimination of an Arc string-tail storage representation.
//!
//! This decoder composes the EXISTING ByteV1 scalar loads, byte GEP and
//! PtrFromParts operations. It is not captured Rust IR or a second evaluator.
//! Its field offsets and ArcInner::data offset must eventually be bound to
//! actual compiler layout facts; neither Rust field order nor a fixed header
//! size is assumed here. In particular, a ContainerLen header is not a str.
//!
//! The profile is LE64. The metadata slot is read as a U64 representation word,
//! not as an implicit conversion from the distinct nominal Usize64 type. Native
//! field/type binding, pointer provenance, LazyLock initialization, Arc sharing
//! and allocation-ledger fidelity remain OPEN. A correct string tail alone is
//! not a valid Name: the Str tag, anonymous parent, cached hash and enclosing
//! Expr/levels/meta invariants are separate obligations. These definitions do
//! not grant allocation, native-admission or whole-Name validity authority.

use crate::spec::{SpecError, Specification};

const MEMORY_RESULT: &str = "IRByteMemoryResultV1";
const STEP: &str = "IRStepResult";
const OPTION: &str = "IROption IRBuiltinNameAtomV1";
const U64: &str = "IRTy.uint_ 64";
const U8: &str = "IRTy.uint_ 8";
const HEADER: &str = "Nat.succ headerPred";
const POINTER_ADDRESS: &str = "Nat.add objectBase pointerOffset";
const LENGTH_ADDRESS: &str = "Nat.add objectBase metadataOffset";
const TAIL: &str = "Nat.add (Nat.succ headerPred) dataOffset";

fn layout(ty: &str, size: usize) -> String {
    format!("IRByteLayoutV1.mk ({ty}) {size} {size} (@IRList.nil IRTy) (@IRList.nil Nat)")
}

fn found(ty: &str, size: usize) -> String {
    format!(
        "@Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ({ty}))
    (@IROption.some IRByteLayoutV1 ({}))",
        layout(ty, size)
    )
}

fn load(ty: &str, address: &str) -> String {
    format!("ir_byte_load_v1 ctx ({ty}) (IRScalar.ptr_ ({address})) 8 Bool.false mem")
}

fn gep(base: &str) -> String {
    format!(
        "ir_byte_gep_v1 ctx ({U8}) ({base})
    (@IRList.cons IRScalar (IRScalar.int_ dataOffset) (@IRList.nil IRScalar)) Bool.true mem"
    )
}

fn value(value: &str) -> String {
    format!("IRByteMemoryResultV1.value ({value}) mem")
}

fn fault(kind: &str, code: &str) -> String {
    format!("IRByteMemoryResultV1.fault (IROutcome.{kind} IRFault.{code}) mem")
}

fn refl(ty: &str, value: &str) -> String {
    format!("@Eq.refl ({ty}) ({value})")
}

fn trans(ty: &str, left: &str, middle: &str, right: &str, first: &str, second: &str) -> String {
    format!("@Eq.trans ({ty}) ({left}) ({middle}) ({right})\n  ({first})\n  ({second})")
}

fn congr(a: &str, b: &str, f: &str, left: &str, right: &str, proof: &str) -> String {
    format!("ir_eq_cong ({a}) ({b}) ({f}) ({left}) ({right})\n  ({proof})")
}

fn and(a: &str, b: &str, first: &str, second: &str) -> String {
    format!("ir_byte_function_and_true_v1 ({a}) ({b}) ({first}) ({second})")
}

fn bool_case(ty: &str, guard: &str, failure: &str, success: &str) -> String {
    format!("@Bool.rec (fun (_ : Bool) => {ty}) ({failure}) ({success}) ({guard})")
}

fn true_rule(
    ty: &str,
    guard: &str,
    failure: &str,
    success: &str,
    expected: &str,
    h: &str,
    step: &str,
) -> String {
    format!(
        "ir_byte_case_true_v1 ({ty}) ({guard}) ({failure}) ({success}) ({expected}) ({h}) ({step})"
    )
}

fn some_case(a: &str, b: &str, option: &str, failure: &str, parameter: &str, body: &str) -> String {
    format!(
        "@IROption.rec ({a}) (fun (_ : IROption ({a})) => {b}) ({failure})
  (fun ({parameter} : {a}) => {body}) ({option})"
    )
}

#[allow(clippy::too_many_arguments)]
fn some_rule(
    a: &str,
    b: &str,
    option: &str,
    v: &str,
    failure: &str,
    parameter: &str,
    body: &str,
    expected: &str,
    h: &str,
    step: &str,
) -> String {
    format!(
        "ir_byte_case_some_v1 ({a}) ({b}) ({option}) ({v}) ({failure})
  (fun ({parameter} : {a}) => {body}) ({expected}) ({h}) ({step})"
    )
}

fn bound(word: &str, proof: &str) -> String {
    format!("ir_byte_ltb_of_lt_v1 ({word}) ir_byte_limit_v1 {proof}")
}

fn scalar_load_source(pointer: bool) -> String {
    let (name, ty, parameters, word, scalar, decoded, fits) = if pointer {
        (
            "pointer",
            "IRTy.ptr_",
            "(headerPred : Nat)",
            HEADER.to_owned(),
            format!("IRScalar.ptr_ ({HEADER})"),
            "ir_byte_pointer_decode_word_v1 ctx headerPred".to_owned(),
            "ir_byte_pointer_value_fits_v1 ctx headerPred wordBound".to_owned(),
        )
    } else {
        (
            "length",
            U64,
            "(length : Nat)",
            "length".to_owned(),
            "IRScalar.int_ length".to_owned(),
            "@Eq.refl (IROption IRScalar) (@IROption.some IRScalar (IRScalar.int_ length))"
                .to_owned(),
            format!(
                "ir_byte_u64_value_fits_v1 ctx length ({})",
                bound("length", "wordBound")
            ),
        )
    };
    let actual = load(ty, "address");
    let alignment = format!(
        "ir_byte_effective_align_v1 8 (ir_byte_layout_align_v1 ({}))",
        layout(ty, 8)
    );
    let middle = format!("ir_byte_load_at_v1 ctx ({ty}) address 8 ({alignment}) mem");
    let expected = value(&scalar);
    let dispatch = format!(
        "ir_byte_load_dispatch_eight_v1 ctx ({ty}) (IRScalar.ptr_ address) 8 mem
  ({}) address (@Eq.refl (IROption Nat) (@IROption.some Nat 8)) layoutFound
  (@Eq.refl Bool Bool.true) (ir_byte_pointer_address_bounded_v1 address addressBound)",
        layout(ty, 8)
    );
    let read = format!("ir_byte_u64_rep_read_v1 mem address ({word}) wordBound rep");
    let access = format!(
        "ir_byte_load_at_rule_v1 ctx ({ty}) address 8 ({alignment}) mem
  ({word}) ({scalar}) accessible ({read}) ({decoded}) ({fits})"
    );
    format!("def ir_byte_arc_tail_{name}_load_v1
  (ctx : IRByteContextV1) (mem : IRByteMemoryV1) (address : Nat) {parameters}
  (addressBound : Nat.lt address ir_byte_limit_v1)
  (wordBound : Nat.lt ({word}) ir_byte_limit_v1)
  (layoutFound : {})
  (accessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address 8 ({alignment})) Bool.true)
  (rep : ir_byte_u64_rep_v1 mem address ({word})) :
  @Eq {MEMORY_RESULT} ({actual}) ({expected}) :=\n{}",
        found(ty, 8), trans(MEMORY_RESULT, &actual, &middle, &expected, &dispatch, &access))
}

fn gep_guard(delta: &str) -> String {
    format!("Bool.and (ir_nat_pos ({HEADER}))
  (Bool.and (ir_nat_ltb ({delta}) ir_byte_limit_v1)
    (Bool.and (ir_nat_ltb (Nat.add ({HEADER}) ({delta})) ir_byte_limit_v1)
      (Bool.or (Bool.not Bool.true)
        (ir_byte_same_allocation_v1 (ir_byte_mem_allocs_v1 mem) ({HEADER}) (Nat.add ({HEADER}) ({delta}))))))")
}

fn gep_source() -> String {
    let expected = value(&format!("ir_byte_pointer_value_v1 ({TAIL})"));
    let failed = fault("ub", "bad_addr");
    let same =
        format!("ir_byte_same_allocation_v1 (ir_byte_mem_allocs_v1 mem) ({HEADER}) ({TAIL})");
    let tail_guard = format!("ir_nat_ltb ({TAIL}) ir_byte_limit_v1");
    let tail_proof = and(
        &tail_guard,
        &same,
        &bound(TAIL, "tailBound"),
        "sameAllocation",
    );
    let delta_guard = "ir_nat_ltb dataOffset ir_byte_limit_v1";
    let delta_proof = and(
        delta_guard,
        &format!("Bool.and ({tail_guard}) ({same})"),
        &bound("dataOffset", "offsetWordBound"),
        &tail_proof,
    );
    let guard_proof = and(
        &format!("ir_nat_pos ({HEADER})"),
        &format!("Bool.and ({delta_guard}) (Bool.and ({tail_guard}) ({same}))"),
        "@Eq.refl Bool Bool.true",
        &delta_proof,
    );
    let at_proof = format!(
        "@Eq.subst Nat
  (fun (delta : Nat) => @Eq {MEMORY_RESULT} ({}) ({expected}))
  dataOffset (Nat.mul 1 dataOffset)
  (@Eq.symm Nat (Nat.mul 1 dataOffset) dataOffset
    (@Eq.trans Nat (Nat.mul 1 dataOffset) (Nat.mul dataOffset 1) dataOffset
      (Nat.mul_comm 1 dataOffset) (Nat.mul_one dataOffset)))
  ({})",
        bool_case(
            MEMORY_RESULT,
            &gep_guard("delta"),
            &failed,
            &value(&format!(
                "ir_byte_pointer_value_v1 (Nat.add ({HEADER}) delta)"
            ))
        ),
        true_rule(
            MEMORY_RESULT,
            &gep_guard("dataOffset"),
            &failed,
            &expected,
            &expected,
            &guard_proof,
            &refl(MEMORY_RESULT, &expected)
        )
    );

    let index_option = "ir_byte_gep_index_v1 (IRScalar.int_ dataOffset)";
    let index_proof = true_rule(
        "IROption Nat",
        "ir_nat_ltb dataOffset 9223372036854775808",
        "@IROption.none Nat",
        "@IROption.some Nat dataOffset",
        "@IROption.some Nat dataOffset",
        "ir_byte_ltb_of_lt_v1 dataOffset 9223372036854775808 offsetSignedBound",
        "@Eq.refl (IROption Nat) (@IROption.some Nat dataOffset)",
    );
    let indices = "ir_byte_gep_indices_v1 (@IRList.cons IRScalar (IRScalar.int_ dataOffset) (@IRList.nil IRScalar))";
    let index_body = bool_case(
        "IROption Nat",
        "ir_nat_ltb (Nat.add index 0) ir_byte_limit_v1",
        "@IROption.none Nat",
        "@IROption.some Nat (Nat.add index 0)",
    );
    let indices_proof = some_rule(
        "Nat",
        "IROption Nat",
        index_option,
        "dataOffset",
        "@IROption.none Nat",
        "index",
        &index_body,
        "@IROption.some Nat dataOffset",
        &index_proof,
        &true_rule(
            "IROption Nat",
            delta_guard,
            "@IROption.none Nat",
            "@IROption.some Nat dataOffset",
            "@IROption.some Nat dataOffset",
            &bound("dataOffset", "offsetWordBound"),
            "@Eq.refl (IROption Nat) (@IROption.some Nat dataOffset)",
        ),
    );

    let pointer = format!("ir_byte_pointer_address_v1 (IRScalar.ptr_ ({HEADER}))");
    let pointer_body =
        "ir_byte_gep_at_v1 address (ir_byte_layout_size_v1 layout) index Bool.true mem";
    let pointer_case = some_case(
        "Nat",
        MEMORY_RESULT,
        &pointer,
        &fault("type_error", "not_ptr"),
        "address",
        pointer_body,
    );
    let indices_case = some_case(
        "Nat",
        MEMORY_RESULT,
        indices,
        &fault("unmodelled", "width_bounded"),
        "index",
        &pointer_case,
    );
    let layout_guard = "Bool.and (ir_nat_pos (ir_byte_layout_size_v1 layout)) (ir_nat_ltb (ir_byte_layout_size_v1 layout) ir_byte_limit_v1)";
    let layout_body = bool_case(
        MEMORY_RESULT,
        layout_guard,
        &fault("unmodelled", "width_bounded"),
        &indices_case,
    );
    // Specialize only the captured byte layout, not any Rust struct layout.
    let byte_layout = layout(U8, 1);
    let specialized_pointer = pointer_case.replace(" layout)", &format!(" ({byte_layout}))"));
    let specialized_indices = indices_case.replace(" layout)", &format!(" ({byte_layout}))"));
    let specialized_guard = layout_guard.replace("layout)", &format!("({byte_layout}))"));
    let pointer_proof = some_rule(
        "Nat",
        MEMORY_RESULT,
        &pointer,
        HEADER,
        &fault("type_error", "not_ptr"),
        "address",
        "ir_byte_gep_at_v1 address 1 dataOffset Bool.true mem",
        &expected,
        "ir_byte_pointer_address_bounded_v1 (Nat.succ headerPred) headerBound",
        &at_proof,
    );
    let indices_proof = some_rule(
        "Nat",
        MEMORY_RESULT,
        indices,
        "dataOffset",
        &fault("unmodelled", "width_bounded"),
        "index",
        &specialized_pointer,
        &expected,
        &indices_proof,
        &pointer_proof,
    );
    let layout_proof = true_rule(
        MEMORY_RESULT,
        &specialized_guard,
        &fault("unmodelled", "width_bounded"),
        &specialized_indices,
        &expected,
        "@Eq.refl Bool Bool.true",
        &indices_proof,
    );
    let proof = some_rule(
        "IRByteLayoutV1",
        MEMORY_RESULT,
        &format!("ir_byte_layout_v1 ctx ({U8})"),
        &byte_layout,
        &fault("unmodelled", "width_bounded"),
        "layout",
        &layout_body,
        &expected,
        "byteLayout",
        &layout_proof,
    );
    format!("def ir_byte_arc_tail_gep_v1
  (ctx : IRByteContextV1) (mem : IRByteMemoryV1) (headerPred dataOffset : Nat)
  (headerBound : Nat.lt ({HEADER}) ir_byte_limit_v1)
  (offsetSignedBound : Nat.lt dataOffset 9223372036854775808)
  (offsetWordBound : Nat.lt dataOffset ir_byte_limit_v1)
  (tailBound : Nat.lt ({TAIL}) ir_byte_limit_v1)
  (byteLayout : {})
  (sameAllocation : @Eq Bool (ir_byte_same_allocation_v1 (ir_byte_mem_allocs_v1 mem) ({HEADER}) ({TAIL})) Bool.true) :
  @Eq {MEMORY_RESULT} ({}) ({expected}) :=\n{proof}", found(U8, 1), gep(&format!("IRScalar.ptr_ ({HEADER})")))
}

const DECODERS: &[&str] = &[
    r"def ir_byte_arc_tail_assemble_v1 (ctx : IRByteContextV1) (metadata : IRScalar)
  (result : IRByteMemoryResultV1) : IRStepResult :=
match result with
| IRByteMemoryResultV1.value data memory =>
  ir_byte_ptrfromparts_eval_v1 ctx IRTy.fatstr_ (IRTy.uint_ 64) data metadata
| IRByteMemoryResultV1.fault outcome memory => IRStepResult.fault outcome",
    r"def ir_byte_arc_tail_after_length_v1 (ctx : IRByteContextV1) (header : IRScalar)
  (dataOffset : Nat) (result : IRByteMemoryResultV1) : IRStepResult :=
match result with
| IRByteMemoryResultV1.value metadata memory =>
  ir_byte_arc_tail_assemble_v1 ctx metadata
    (ir_byte_gep_v1 ctx (IRTy.uint_ 8) header
      (@IRList.cons IRScalar (IRScalar.int_ dataOffset) (@IRList.nil IRScalar)) Bool.true memory)
| IRByteMemoryResultV1.fault outcome memory => IRStepResult.fault outcome",
    r"def ir_byte_arc_tail_after_pointer_v1 (ctx : IRByteContextV1)
  (metadataAddress dataOffset : Nat) (result : IRByteMemoryResultV1) : IRStepResult :=
match result with
| IRByteMemoryResultV1.value header memory =>
  ir_byte_arc_tail_after_length_v1 ctx header dataOffset
    (ir_byte_load_v1 ctx (IRTy.uint_ 64) (IRScalar.ptr_ metadataAddress) 8 Bool.false memory)
| IRByteMemoryResultV1.fault outcome memory => IRStepResult.fault outcome",
    r"def ir_byte_arc_tail_project_v1 (ctx : IRByteContextV1) (mem : IRByteMemoryV1)
  (objectBase pointerOffset metadataOffset dataOffset : Nat) : IRStepResult :=
ir_byte_arc_tail_after_pointer_v1 ctx (Nat.add objectBase metadataOffset) dataOffset
  (ir_byte_load_v1 ctx IRTy.ptr_ (IRScalar.ptr_ (Nat.add objectBase pointerOffset)) 8 Bool.false mem)",
    r"def ir_byte_arc_tail_observe_result_v1 (mem : IRByteMemoryV1)
  (result : IRStepResult) : IROption IRBuiltinNameAtomV1 :=
match result with
| IRStepResult.value scalar => ir_byte_builtin_name_atom_v1 mem IRTy.fatstr_ scalar
| IRStepResult.fault outcome => @IROption.none IRBuiltinNameAtomV1",
    r"def ir_byte_arc_tail_observe_v1 (ctx : IRByteContextV1) (mem : IRByteMemoryV1)
  (objectBase pointerOffset metadataOffset dataOffset : Nat) : IROption IRBuiltinNameAtomV1 :=
ir_byte_arc_tail_observe_result_v1 mem
  (ir_byte_arc_tail_project_v1 ctx mem objectBase pointerOffset metadataOffset dataOffset)",
];

fn telescope(length: Option<usize>) -> String {
    let length_parameter = if length.is_none() { " length" } else { "" };
    let length_word = length.map_or_else(|| "length".to_owned(), |n| n.to_string());
    format!("(ctx : IRByteContextV1) (mem : IRByteMemoryV1)
  (objectBase pointerOffset metadataOffset headerPred dataOffset{length_parameter} : Nat)
  (pointerAddressBound : Nat.lt ({POINTER_ADDRESS}) ir_byte_limit_v1)
  (metadataAddressBound : Nat.lt ({LENGTH_ADDRESS}) ir_byte_limit_v1)
  (headerBound : Nat.lt ({HEADER}) ir_byte_limit_v1)
  (lengthBound : Nat.lt {length_word} ir_byte_limit_v1)
  (offsetSignedBound : Nat.lt dataOffset 9223372036854775808)
  (offsetWordBound : Nat.lt dataOffset ir_byte_limit_v1)
  (tailBound : Nat.lt ({TAIL}) ir_byte_limit_v1)
  (pointerLayout : {})
  (lengthLayout : {})
  (byteLayout : {})
  (pointerAccessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem)
    ({POINTER_ADDRESS}) 8 (ir_byte_effective_align_v1 8 (ir_byte_layout_align_v1 ({})))) Bool.true)
  (lengthAccessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem)
    ({LENGTH_ADDRESS}) 8 (ir_byte_effective_align_v1 8 (ir_byte_layout_align_v1 ({})))) Bool.true)
  (pointerRep : ir_byte_u64_rep_v1 mem ({POINTER_ADDRESS}) ({HEADER}))
  (lengthRep : ir_byte_u64_rep_v1 mem ({LENGTH_ADDRESS}) {length_word})
  (sameAllocation : @Eq Bool (ir_byte_same_allocation_v1 (ir_byte_mem_allocs_v1 mem) ({HEADER}) ({TAIL})) Bool.true)",
        found("IRTy.ptr_", 8), found(U64, 8), found(U8, 1), layout("IRTy.ptr_", 8), layout(U64, 8))
}

fn project_source() -> String {
    let actual =
        "ir_byte_arc_tail_project_v1 ctx mem objectBase pointerOffset metadataOffset dataOffset";
    let pointer_result = value(&format!("IRScalar.ptr_ ({HEADER})"));
    let length_result = value("IRScalar.int_ length");
    let tail_result = value(&format!("ir_byte_pointer_value_v1 ({TAIL})"));
    let expected = format!("IRStepResult.value (IRScalar.fat_ ({TAIL}) length)");
    let pointer_continuation =
        format!("ir_byte_arc_tail_after_pointer_v1 ctx ({LENGTH_ADDRESS}) dataOffset");
    let length_continuation =
        format!("ir_byte_arc_tail_after_length_v1 ctx (IRScalar.ptr_ ({HEADER})) dataOffset");
    let tail_continuation = "ir_byte_arc_tail_assemble_v1 ctx (IRScalar.int_ length)";
    let middle1 = format!("{pointer_continuation} ({pointer_result})");
    let middle2 = format!("{length_continuation} ({length_result})");
    let middle3 = format!("{tail_continuation} ({tail_result})");
    let pointer_proof = format!(
        "ir_byte_arc_tail_pointer_load_v1 ctx mem ({POINTER_ADDRESS}) headerPred
  pointerAddressBound headerBound pointerLayout pointerAccessible pointerRep"
    );
    let length_proof = format!(
        "ir_byte_arc_tail_length_load_v1 ctx mem ({LENGTH_ADDRESS}) length
  metadataAddressBound lengthBound lengthLayout lengthAccessible lengthRep"
    );
    let gep_proof = "ir_byte_arc_tail_gep_v1 ctx mem headerPred dataOffset headerBound
  offsetSignedBound offsetWordBound tailBound byteLayout sameAllocation";
    let parts_proof =
        format!("ir_byte_fatstr_fromparts_v1 ctx ({TAIL}) length tailBound lengthBound");
    let proof3 = trans(
        STEP,
        &middle2,
        &middle3,
        &expected,
        &congr(
            MEMORY_RESULT,
            STEP,
            tail_continuation,
            &gep(&format!("IRScalar.ptr_ ({HEADER})")),
            &tail_result,
            gep_proof,
        ),
        &parts_proof,
    );
    let proof2 = trans(
        STEP,
        &middle1,
        &middle2,
        &expected,
        &congr(
            MEMORY_RESULT,
            STEP,
            &length_continuation,
            &load(U64, LENGTH_ADDRESS),
            &length_result,
            &length_proof,
        ),
        &proof3,
    );
    let proof = trans(
        STEP,
        actual,
        &middle1,
        &expected,
        &congr(
            MEMORY_RESULT,
            STEP,
            &pointer_continuation,
            &load("IRTy.ptr_", POINTER_ADDRESS),
            &pointer_result,
            &pointer_proof,
        ),
        &proof2,
    );
    format!(
        "def ir_byte_arc_tail_project_input_v1 {} :
  @Eq {STEP} ({actual}) ({expected}) :=\n{proof}",
        telescope(None)
    )
}

fn observer_source(name: &str, bytes: &[u8]) -> String {
    let length = bytes.len();
    let byte_address =
        |offset: usize| (0..offset).fold(format!("({TAIL})"), |a, _| format!("(Nat.succ {a})"));
    let byte_premises = bytes.iter().enumerate().map(|(i, byte)| format!("\n  (byte{i} : @Eq (IROption Nat) (ir_byte_mem_bytes_v1 mem {}) (@IROption.some Nat {byte}))", byte_address(i))).collect::<String>();
    let args = (0..length).map(|i| format!(" byte{i}")).collect::<String>();
    let actual =
        "ir_byte_arc_tail_observe_v1 ctx mem objectBase pointerOffset metadataOffset dataOffset";
    let projected = format!("IRStepResult.value (IRScalar.fat_ ({TAIL}) {length})");
    let middle =
        format!("ir_byte_builtin_name_atom_v1 mem IRTy.fatstr_ (IRScalar.fat_ ({TAIL}) {length})");
    let expected = format!("@IROption.some IRBuiltinNameAtomV1 IRBuiltinNameAtomV1.{name}_");
    let projection = format!("ir_byte_arc_tail_project_input_v1 ctx mem objectBase pointerOffset metadataOffset headerPred dataOffset {length}
  pointerAddressBound metadataAddressBound headerBound lengthBound offsetSignedBound offsetWordBound tailBound
  pointerLayout lengthLayout byteLayout pointerAccessible lengthAccessible pointerRep lengthRep sameAllocation");
    let transport = congr(
        STEP,
        OPTION,
        "ir_byte_arc_tail_observe_result_v1 mem",
        "ir_byte_arc_tail_project_v1 ctx mem objectBase pointerOffset metadataOffset dataOffset",
        &projected,
        &projection,
    );
    // Destructure memory to avoid assuming eta for the reflected record.
    let observer = format!("@IRByteMemoryV1.rec
  (fun (memory : IRByteMemoryV1) =>
    @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 memory) ({TAIL}) {length} 1) Bool.true ->
    {} @Eq ({OPTION}) (ir_byte_builtin_name_atom_v1 memory IRTy.fatstr_ (IRScalar.fat_ ({TAIL}) {length})) ({expected}))
  (fun (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat) (next : Nat) =>
    ir_byte_builtin_{name}_input_v1 allocs bytes next ({TAIL}) tailBound)
  mem tailAccessible{args}",
        bytes.iter().enumerate().map(|(i, byte)| format!("@Eq (IROption Nat) (ir_byte_mem_bytes_v1 memory {}) (@IROption.some Nat {byte}) ->\n    ", byte_address(i))).collect::<String>());
    format!("def ir_byte_arc_tail_{name}_input_v1 {}
  (tailAccessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) ({TAIL}) {length} 1) Bool.true)
  {byte_premises} :
  @Eq ({OPTION}) ({actual}) ({expected}) :=\n{}", telescope(Some(length)), trans(OPTION, actual, &middle, &expected, &transport, &observer))
}

impl Specification {
    pub(super) fn add_eval_ir_byte_arc_tail_v1(&mut self) -> Result<(), SpecError> {
        for source in [
            scalar_load_source(true),
            scalar_load_source(false),
            gep_source(),
        ] {
            self.add_recursive_def(&source, "Checked input-to-operation rule for the actual typed LE64 load or inbounds byte GEP; no successful-result premise.")?;
        }
        for source in DECODERS {
            self.add_recursive_def(source, "Conditional Arc-tail storage decoder composing existing operations, not captured Rust execution or authenticated source layout/provenance.")?;
        }
        self.add_recursive_def(&project_source(), "Raw field-byte representation eliminates to actual loads, offset GEP and FatStr assembly; compiler field/data offsets and native provenance remain open attachment obligations.")?;
        for (name, bytes) in [("nat", b"Nat".as_slice()), ("string", b"String".as_slice())] {
            self.add_recursive_def(&observer_source(name, bytes), "Exact builtin atom from raw field storage and initialized live tail bytes through the actual projection operations; not whole-Name/Expr validity.")?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_arc_tail_tests.rs"]
mod tests;
