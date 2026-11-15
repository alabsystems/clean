// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked rules for the actual public typed byte accesses. Premises name the
//! real layout, pointer and accessibility checks, not an assumed load answer.
//! The concrete scalar consumers discharge value encoding/decoding and use the
//! universal eight-byte codec. Allocation/lifetime and provider preservation
//! remain explicit obligations; no native admission authority is constructed.

use crate::spec::{SpecError, Specification};

const RESULT: &str = "IRByteMemoryResultV1";
const LIMIT: &str = "18446744073709551616";

const CASE_TRUE: &str = r"def ir_byte_case_true_v1 (A : Type) (guard : Bool)
  (failure : A) (success : A) (expected : A)
  (h : @Eq Bool guard Bool.true) (step : @Eq A success expected) :
  @Eq A (@Bool.rec (fun (_ : Bool) => A) failure success guard) expected :=
@Eq.subst Bool
  (fun (g : Bool) => @Eq A (@Bool.rec (fun (_ : Bool) => A) failure success g) expected)
  Bool.true guard (@Eq.symm Bool guard Bool.true h) step";

const CASE_SOME: &str = r"def ir_byte_case_some_v1 (A : Type) (B : Type) (option : IROption A)
  (value : A) (failure : B) (success : A -> B) (expected : B)
  (h : @Eq (IROption A) option (@IROption.some A value))
  (step : @Eq B (success value) expected) :
  @Eq B (@IROption.rec A (fun (_ : IROption A) => B) failure success option) expected :=
@Eq.subst (IROption A)
  (fun (o : IROption A) => @Eq B
    (@IROption.rec A (fun (_ : IROption A) => B) failure success o) expected)
  (@IROption.some A value) option
  (@Eq.symm (IROption A) option (@IROption.some A value) h) step";

const RELOAD: &str = r"def ir_byte_reload_v1 (ctx : IRByteContextV1) (ty : IRTy)
  (ptr : IRScalar) (align : Nat) (result : IRByteMemoryResultV1) : IRByteMemoryResultV1 :=
match result with
| IRByteMemoryResultV1.value ignored memory => ir_byte_load_v1 ctx ty ptr align Bool.false memory
| IRByteMemoryResultV1.fault outcome memory => IRByteMemoryResultV1.fault outcome memory";

const POINTER_ADDRESS: &str = r"def ir_byte_pointer_address_bounded_v1 (address : Nat)
  (bounded : Nat.lt address ir_byte_limit_v1) :
  @Eq (IROption Nat) (ir_byte_pointer_address_v1 (IRScalar.ptr_ address)) (@IROption.some Nat address) :=
ir_byte_case_true_v1 (IROption Nat) (ir_nat_ltb address ir_byte_limit_v1)
  (@IROption.none Nat) (@IROption.some Nat address) (@IROption.some Nat address)
  (ir_byte_ltb_of_lt_v1 address ir_byte_limit_v1 bounded)
  (@Eq.refl (IROption Nat) (@IROption.some Nat address))";

const POINTER_FITS: &str = r"def ir_byte_pointer_value_fits_v1 (ctx : IRByteContextV1) (predecessor : Nat)
  (bounded : Nat.lt (Nat.succ predecessor) ir_byte_limit_v1) :
  @Eq Bool (ir_byte_value_matches_v1 ctx IRTy.ptr_ (IRScalar.ptr_ (Nat.succ predecessor))) Bool.true :=
ir_byte_ltb_of_lt_v1 (Nat.succ predecessor) ir_byte_limit_v1 bounded";

const POINTER_ENCODE: &str = r"def ir_byte_pointer_scalar_word_v1 (ctx : IRByteContextV1) (predecessor : Nat)
  (bounded : Nat.lt (Nat.succ predecessor) ir_byte_limit_v1) :
  @Eq (IROption Nat) (ir_byte_scalar_word_v1 ctx (IRScalar.ptr_ (Nat.succ predecessor)))
    (@IROption.some Nat (Nat.succ predecessor)) :=
ir_byte_case_true_v1 (IROption Nat) (ir_nat_ltb (Nat.succ predecessor) ir_byte_limit_v1)
  (@IROption.none Nat) (@IROption.some Nat (Nat.succ predecessor)) (@IROption.some Nat (Nat.succ predecessor))
  (ir_byte_ltb_of_lt_v1 (Nat.succ predecessor) ir_byte_limit_v1 bounded)
  (@Eq.refl (IROption Nat) (@IROption.some Nat (Nat.succ predecessor)))";

const POINTER_DECODE: &str = r"def ir_byte_pointer_decode_word_v1 (ctx : IRByteContextV1) (predecessor : Nat) :
  @Eq (IROption IRScalar) (ir_byte_decode_word_v1 ctx IRTy.ptr_ (Nat.succ predecessor))
    (@IROption.some IRScalar (IRScalar.ptr_ (Nat.succ predecessor))) :=
ir_eq_cong Bool (IROption IRScalar)
  (fun (zero : Bool) => @IROption.some IRScalar
    (@Bool.rec (fun (_ : Bool) => IRScalar) (IRScalar.ptr_ (Nat.succ predecessor)) IRScalar.nullptr_ zero))
  (ir_nat_eqb (Nat.succ predecessor) 0) Bool.false (ir_byte_eqb_succ_zero_v1 predecessor)";

fn eq(ty: &str, left: &str, right: &str) -> String {
    format!("@Eq ({ty}) ({left}) ({right})")
}
fn refl(ty: &str, value: &str) -> String {
    format!("@Eq.refl ({ty}) ({value})")
}
fn trans(ty: &str, left: &str, middle: &str, right: &str, first: &str, second: &str) -> String {
    format!("@Eq.trans ({ty}) ({left}) ({middle}) ({right}) ({first}) ({second})")
}
fn bool_case(ty: &str, failure: &str, success: &str, guard: &str) -> String {
    format!("@Bool.rec (fun (_ : Bool) => {ty}) ({failure}) ({success}) ({guard})")
}
fn some_case(a: &str, b: &str, failure: &str, parameter: &str, body: &str, option: &str) -> String {
    format!("@IROption.rec ({a}) (fun (_ : IROption ({a})) => {b}) ({failure}) (fun ({parameter} : {a}) => {body}) ({option})")
}
fn true_rule(
    ty: &str,
    failure: &str,
    success: &str,
    guard: &str,
    h: &str,
    expected: &str,
    step: &str,
) -> String {
    format!(
        "ir_byte_case_true_v1 ({ty}) ({guard}) ({failure}) ({success}) ({expected}) ({h}) ({step})"
    )
}
#[allow(clippy::too_many_arguments)]
fn some_rule(
    a: &str,
    b: &str,
    failure: &str,
    parameter: &str,
    body: &str,
    option: &str,
    value: &str,
    h: &str,
    expected: &str,
    step: &str,
) -> String {
    format!("ir_byte_case_some_v1 ({a}) ({b}) ({option}) ({value}) ({failure}) (fun ({parameter} : {a}) => {body}) ({expected}) ({h}) ({step})")
}
fn fault(kind: &str, code: &str, memory: &str) -> String {
    format!("IRByteMemoryResultV1.fault (IROutcome.{kind} IRFault.{code}) ({memory})")
}
fn result(value: &str, memory: &str) -> String {
    format!("IRByteMemoryResultV1.value ({value}) ({memory})")
}
fn written(memory: &str, address: &str, word: &str) -> String {
    format!("IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 ({memory})) (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 ({memory})) ({address}) 8 ({word})) (ir_byte_mem_next_v1 ({memory}))")
}
fn bound(word: &str) -> String {
    format!("ir_byte_ltb_of_lt_v1 ({word}) {LIMIT} bounded")
}

fn store_word_case(word: &str) -> String {
    bool_case(
        RESULT,
        &fault("type_error", "width_bounded", "mem"),
        &result("IRScalar.unit_", &written("mem", "address", word)),
        &format!("ir_nat_ltb ({word}) (ir_nat_pow2 (Nat.mul 8 8))"),
    )
}
fn store_option_case() -> String {
    some_case(
        "Nat",
        RESULT,
        &fault("type_error", "width_bounded", "mem"),
        "coded",
        &store_word_case("coded"),
        "ir_byte_scalar_word_v1 ctx value",
    )
}
fn store_at_source() -> String {
    let next = written("mem", "address", "word");
    let expected = result("IRScalar.unit_", &next);
    let canonical = true_rule(
        RESULT,
        &fault("type_error", "width_bounded", "mem"),
        &expected,
        "ir_nat_ltb word (ir_nat_pow2 (Nat.mul 8 8))",
        &bound("word"),
        &expected,
        &refl(RESULT, &expected),
    );
    let encode = some_rule(
        "Nat",
        RESULT,
        &fault("type_error", "width_bounded", "mem"),
        "coded",
        &store_word_case("coded"),
        "ir_byte_scalar_word_v1 ctx value",
        "word",
        "encoded",
        &expected,
        &canonical,
    );
    let fits = true_rule(
        RESULT,
        &fault("type_error", "width_bounded", "mem"),
        &store_option_case(),
        "ir_byte_value_matches_v1 ctx ty value",
        "fits",
        &expected,
        &encode,
    );
    let body = bool_case(
        RESULT,
        &fault("type_error", "width_bounded", "mem"),
        &store_option_case(),
        "ir_byte_value_matches_v1 ctx ty value",
    );
    let proof = true_rule(
        RESULT,
        &fault("ub", "bad_addr", "mem"),
        &body,
        "ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address 8 align",
        "accessible",
        &expected,
        &fits,
    );
    format!("def ir_byte_store_at_eight_rule_v1 (ctx : IRByteContextV1) (ty : IRTy) (address : Nat)\n\
      (value : IRScalar) (align : Nat) (mem : IRByteMemoryV1) (word : Nat)\n\
      (accessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address 8 align) Bool.true)\n\
      (fits : @Eq Bool (ir_byte_value_matches_v1 ctx ty value) Bool.true)\n\
      (encoded : @Eq (IROption Nat) (ir_byte_scalar_word_v1 ctx value) (@IROption.some Nat word))\n\
      (bounded : Nat.lt word {LIMIT}) :\n{} :=\n{proof}",
        eq(RESULT, "ir_byte_store_at_v1 ctx ty address value 8 align mem", &expected))
}

fn load_value_case(value: &str) -> String {
    bool_case(
        RESULT,
        &fault("ub", "width_bounded", "mem"),
        &result(value, "mem"),
        &format!("ir_byte_value_matches_v1 ctx ty ({value})"),
    )
}
fn load_decode_case(word: &str) -> String {
    some_case(
        "IRScalar",
        RESULT,
        &fault("ub", "width_bounded", "mem"),
        "loaded",
        &load_value_case("loaded"),
        &format!("ir_byte_decode_word_v1 ctx ty ({word})"),
    )
}
fn load_at_source() -> String {
    let expected = result("value", "mem");
    let fits = true_rule(
        RESULT,
        &fault("ub", "width_bounded", "mem"),
        &expected,
        "ir_byte_value_matches_v1 ctx ty value",
        "fits",
        &expected,
        &refl(RESULT, &expected),
    );
    let decoded = some_rule(
        "IRScalar",
        RESULT,
        &fault("ub", "width_bounded", "mem"),
        "loaded",
        &load_value_case("loaded"),
        "ir_byte_decode_word_v1 ctx ty word",
        "value",
        "decoded",
        &expected,
        &fits,
    );
    let read = some_rule(
        "Nat",
        RESULT,
        &fault("ub", "uninit", "mem"),
        "coded",
        &load_decode_case("coded"),
        "ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) size address",
        "word",
        "read",
        &expected,
        &decoded,
    );
    let body = some_case(
        "Nat",
        RESULT,
        &fault("ub", "uninit", "mem"),
        "coded",
        &load_decode_case("coded"),
        "ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) size address",
    );
    let proof = true_rule(
        RESULT,
        &fault("ub", "bad_addr", "mem"),
        &body,
        "ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address size align",
        "accessible",
        &expected,
        &read,
    );
    format!("def ir_byte_load_at_rule_v1 (ctx : IRByteContextV1) (ty : IRTy)\n\
      (address size align : Nat) (mem : IRByteMemoryV1) (word : Nat) (value : IRScalar)\n\
      (accessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address size align) Bool.true)\n\
      (read : @Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) size address) (@IROption.some Nat word))\n\
      (decoded : @Eq (IROption IRScalar) (ir_byte_decode_word_v1 ctx ty word) (@IROption.some IRScalar value))\n\
      (fits : @Eq Bool (ir_byte_value_matches_v1 ctx ty value) Bool.true) :\n{} :=\n{proof}",
        eq(RESULT, "ir_byte_load_at_v1 ctx ty address size align mem", &expected))
}

fn operation(name: &str, size: &str, layout: &str, address: &str, mem: &str) -> String {
    let value = if name == "store" { " value" } else { "" };
    format!("ir_byte_{name}_at_v1 ctx ty ({address}){value} ({size}) (ir_byte_effective_align_v1 align (ir_byte_layout_align_v1 ({layout}))) ({mem})")
}
fn layout_guard(size: &str, layout: &str) -> String {
    format!("Bool.and (ir_nat_eqb ({size}) (ir_byte_layout_size_v1 ({layout}))) (ir_byte_alignment_v1 (ir_byte_layout_align_v1 ({layout})))")
}
fn pointer_case(name: &str, size: &str, layout: &str) -> String {
    some_case(
        "Nat",
        RESULT,
        &fault("type_error", "not_ptr", "mem"),
        "location",
        &operation(name, size, layout, "location", "mem"),
        "ir_byte_pointer_address_v1 ptr",
    )
}
fn layout_case(name: &str, size: &str, layout: &str) -> String {
    bool_case(
        RESULT,
        &fault("type_error", "width_bounded", "mem"),
        &pointer_case(name, size, layout),
        &layout_guard(size, layout),
    )
}
fn layout_option(name: &str, size: &str) -> String {
    some_case(
        "IRByteLayoutV1",
        RESULT,
        &fault("unmodelled", "width_bounded", "mem"),
        "shape",
        &layout_case(name, size, "shape"),
        "ir_byte_layout_v1 ctx ty",
    )
}
fn dispatch_source(name: &str) -> String {
    let expected = operation(name, "8", "layout", "address", "mem");
    let pointer = some_rule(
        "Nat",
        RESULT,
        &fault("type_error", "not_ptr", "mem"),
        "location",
        &operation(name, "8", "layout", "location", "mem"),
        "ir_byte_pointer_address_v1 ptr",
        "address",
        "pointer",
        &expected,
        &refl(RESULT, &expected),
    );
    let valid_layout = true_rule(
        RESULT,
        &fault("type_error", "width_bounded", "mem"),
        &pointer_case(name, "8", "layout"),
        &layout_guard("8", "layout"),
        "valid_layout",
        &expected,
        &pointer,
    );
    let layout = some_rule(
        "IRByteLayoutV1",
        RESULT,
        &fault("unmodelled", "width_bounded", "mem"),
        "shape",
        &layout_case(name, "8", "shape"),
        "ir_byte_layout_v1 ctx ty",
        "layout",
        "layout_found",
        &expected,
        &valid_layout,
    );
    let proof = some_rule(
        "Nat",
        RESULT,
        &fault("unmodelled", "width_bounded", "mem"),
        "size",
        &layout_option(name, "size"),
        "ir_byte_lane_size_v1 ty",
        "8",
        "lane",
        &expected,
        &layout,
    );
    let parameter = if name == "store" {
        " (value : IRScalar)"
    } else {
        ""
    };
    let argument = if name == "store" { " value" } else { "" };
    format!("def ir_byte_{name}_dispatch_eight_v1 (ctx : IRByteContextV1) (ty : IRTy) (ptr : IRScalar){parameter}\n\
      (align : Nat) (mem : IRByteMemoryV1) (layout : IRByteLayoutV1) (address : Nat)\n\
      (lane : @Eq (IROption Nat) (ir_byte_lane_size_v1 ty) (@IROption.some Nat 8))\n\
      (layout_found : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ty) (@IROption.some IRByteLayoutV1 layout))\n\
      (valid_layout : @Eq Bool ({}) Bool.true)\n\
      (pointer : @Eq (IROption Nat) (ir_byte_pointer_address_v1 ptr) (@IROption.some Nat address)) :\n{} :=\n{proof}",
        layout_guard("8", "layout"), eq(RESULT, &format!("ir_byte_{name}_v1 ctx ty ptr{argument} align Bool.false mem"), &expected))
}

fn roundtrip_source() -> String {
    let next = written("mem", "address", "word");
    let stored = result("IRScalar.unit_", &next);
    let expected = result("value", &next);
    let alignment = "ir_byte_effective_align_v1 align (ir_byte_layout_align_v1 layout)";
    let dispatch_store = "ir_byte_store_dispatch_eight_v1 ctx ty ptr value align mem layout address lane layout_found valid_layout pointer";
    let store_at = format!("ir_byte_store_at_eight_rule_v1 ctx ty address value ({alignment}) mem word accessible fits encoded bounded");
    let store = trans(
        RESULT,
        "ir_byte_store_v1 ctx ty ptr value align Bool.false mem",
        &operation("store", "8", "layout", "address", "mem"),
        &stored,
        dispatch_store,
        &store_at,
    );
    let dispatch_load = format!("ir_byte_load_dispatch_eight_v1 ctx ty ptr align ({next}) layout address lane layout_found valid_layout pointer");
    let load_at = format!(
        "ir_byte_load_at_rule_v1 ctx ty address 8 ({alignment}) ({next}) word value accessible\n\
        (ir_byte_read_write_eight_v1 (ir_byte_mem_bytes_v1 mem) address word bounded) decoded fits"
    );
    let load = trans(
        RESULT,
        &format!("ir_byte_load_v1 ctx ty ptr align Bool.false ({next})"),
        &operation("load", "8", "layout", "address", &next),
        &expected,
        &dispatch_load,
        &load_at,
    );
    let proof = trans(RESULT, "ir_byte_reload_v1 ctx ty ptr align (ir_byte_store_v1 ctx ty ptr value align Bool.false mem)",
        &format!("ir_byte_reload_v1 ctx ty ptr align ({stored})"), &expected,
        &format!("ir_eq_cong {RESULT} {RESULT} (fun (operation : {RESULT}) => ir_byte_reload_v1 ctx ty ptr align operation)\n\
          (ir_byte_store_v1 ctx ty ptr value align Bool.false mem) ({stored}) ({store})"), &load);
    format!("def ir_byte_store_reload_eight_v1 (ctx : IRByteContextV1) (ty : IRTy) (ptr value : IRScalar)\n\
      (align : Nat) (mem : IRByteMemoryV1) (layout : IRByteLayoutV1) (address word : Nat)\n\
      (lane : @Eq (IROption Nat) (ir_byte_lane_size_v1 ty) (@IROption.some Nat 8))\n\
      (layout_found : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ty) (@IROption.some IRByteLayoutV1 layout))\n\
      (valid_layout : @Eq Bool ({}) Bool.true)\n\
      (pointer : @Eq (IROption Nat) (ir_byte_pointer_address_v1 ptr) (@IROption.some Nat address))\n\
      (accessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address 8 ({alignment})) Bool.true)\n\
      (fits : @Eq Bool (ir_byte_value_matches_v1 ctx ty value) Bool.true)\n\
      (encoded : @Eq (IROption Nat) (ir_byte_scalar_word_v1 ctx value) (@IROption.some Nat word))\n\
      (decoded : @Eq (IROption IRScalar) (ir_byte_decode_word_v1 ctx ty word) (@IROption.some IRScalar value))\n\
      (bounded : Nat.lt word {LIMIT}) :\n{} :=\n{proof}", layout_guard("8", "layout"),
        eq(RESULT, "ir_byte_reload_v1 ctx ty ptr align (ir_byte_store_v1 ctx ty ptr value align Bool.false mem)", &expected))
}

fn canonical_layout(ty: &str) -> String {
    format!("IRByteLayoutV1.mk ({ty}) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat)")
}

fn layout_eight_source() -> String {
    format!("def ir_byte_canonical_layout_eight_v1 (ty : IRTy) : @Eq Bool ({}) Bool.true := @Eq.refl Bool Bool.true", layout_guard("8", &canonical_layout("ty")))
}

fn lane_eight_source(name: &str, ty: &str) -> String {
    format!("def ir_byte_{name}_lane_eight_v1 : @Eq (IROption Nat) (ir_byte_lane_size_v1 ({ty})) (@IROption.some Nat 8) := @Eq.refl (IROption Nat) (@IROption.some Nat 8)")
}

/// The scalar consumers specialize the shared operational theorem; they do
/// not assume the desired codec/typed-value result. Layout and live aligned
/// destination admission remain facts about the actual execution context.
#[derive(Clone, Copy)]
enum ScalarKind {
    U64,
    I64,
    Ptr,
    Null,
}

fn scalar_roundtrip_source(kind: ScalarKind) -> String {
    let name = match kind {
        ScalarKind::U64 => "u64",
        ScalarKind::I64 => "i64",
        ScalarKind::Ptr => "ptr",
        ScalarKind::Null => "null",
    };
    let (ty, value, word, parameters, canonical, fits, encoded, decoded, bounded) = match kind {
        ScalarKind::U64 | ScalarKind::I64 => {
            let signed = if matches!(kind, ScalarKind::I64) {
                "int_"
            } else {
                "uint_"
            };
            (
                format!("IRTy.{signed} 64"),
                "IRScalar.int_ word".to_owned(),
                "word".to_owned(),
                "(word : Nat)".to_owned(),
                format!("(bounded : Nat.lt word {LIMIT})"),
                format!("ir_byte_{name}_value_fits_v1 ctx word (ir_byte_ltb_of_lt_v1 word (ir_nat_pow2 64) bounded)"),
                refl("IROption Nat", "@IROption.some Nat word"),
                refl(
                    "IROption IRScalar",
                    "@IROption.some IRScalar (IRScalar.int_ word)",
                ),
                "bounded".to_owned(),
            )
        }
        ScalarKind::Ptr => (
            "IRTy.ptr_".to_owned(),
            "IRScalar.ptr_ (Nat.succ predecessor)".to_owned(),
            "Nat.succ predecessor".to_owned(),
            "(predecessor : Nat)".to_owned(),
            format!("(bounded : Nat.lt (Nat.succ predecessor) {LIMIT})"),
            "ir_byte_pointer_value_fits_v1 ctx predecessor bounded".to_owned(),
            "ir_byte_pointer_scalar_word_v1 ctx predecessor bounded".to_owned(),
            "ir_byte_pointer_decode_word_v1 ctx predecessor".to_owned(),
            "bounded".to_owned(),
        ),
        ScalarKind::Null => (
            "IRTy.ptr_".to_owned(),
            "IRScalar.nullptr_".to_owned(),
            "0".to_owned(),
            String::new(),
            String::new(),
            refl("Bool", "Bool.true"),
            refl("IROption Nat", "@IROption.some Nat 0"),
            refl(
                "IROption IRScalar",
                "@IROption.some IRScalar IRScalar.nullptr_",
            ),
            "Nat.zero_lt_succ 18446744073709551615".to_owned(),
        ),
    };
    let layout = canonical_layout(&ty);
    // Keep the exact operational projection in this symbolic premise. Reducing
    // just its natural alignment to 8 makes the elaborator normalize the whole
    // accessibility predicate during conversion, including symbolic minus 2^64.
    // The constructor fixes this projection to 8; no admission fact is added.
    let alignment =
        format!("ir_byte_effective_align_v1 align (ir_byte_layout_align_v1 ({layout}))");
    let lane_name = if matches!(kind, ScalarKind::Null) {
        "ptr"
    } else {
        name
    };
    let next = written("mem", "location", &word);
    let expected = result(&value, &next);
    let actual = format!(
        "ir_byte_reload_v1 ctx ({ty}) (IRScalar.ptr_ location) align\n\
        (ir_byte_store_v1 ctx ({ty}) (IRScalar.ptr_ location) ({value}) align Bool.false mem)"
    );
    format!("def ir_byte_{name}_store_reload_v1 (ctx : IRByteContextV1) (location align : Nat)\n\
      (mem : IRByteMemoryV1) {parameters}\n\
      (location_bounded : Nat.lt location ir_byte_limit_v1) {canonical}\n\
      (layout_found : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ({ty})) (@IROption.some IRByteLayoutV1 ({layout})))\n\
      (accessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) location 8 ({alignment})) Bool.true) :\n{} :=\n\
      ir_byte_store_reload_eight_v1 ctx ({ty}) (IRScalar.ptr_ location) ({value}) align mem ({layout}) location ({word})\n\
        ir_byte_{lane_name}_lane_eight_v1 layout_found (ir_byte_canonical_layout_eight_v1 ({ty}))\n\
        (ir_byte_pointer_address_bounded_v1 location location_bounded) accessible\n\
        ({fits}) ({encoded}) ({decoded}) ({bounded})", eq(RESULT, &actual, &expected))
}

const FUNCTION_LANE: &str = r"def ir_byte_function_lane_eight_v1 (sig : Nat) :
  @Eq (IROption Nat) (ir_byte_lane_size_v1 (IRTy.func_ sig)) (@IROption.some Nat 8) :=
@Eq.refl (IROption Nat) (@IROption.some Nat 8)";

fn function_roundtrip_source() -> String {
    let ty = "IRTy.func_ sig";
    let layout = canonical_layout(ty);
    let binding = "IRByteFunctionV1.mk fid sig address cc imported";
    let next = written("mem", "location", "address");
    let actual = "ir_byte_reload_v1 ctx (IRTy.func_ sig) (IRScalar.ptr_ location) align
      (ir_byte_store_v1 ctx (IRTy.func_ sig) (IRScalar.ptr_ location) (IRScalar.fnptr_ fid) align Bool.false mem)";
    let expected = result("IRScalar.fnptr_ fid", &next);
    format!("def ir_byte_fnptr_store_reload_v1 (ctx : IRByteContextV1) (location align : Nat)\n\
      (mem : IRByteMemoryV1) (fid sig address cc : Nat) (imported : Bool)\n\
      (location_bounded : Nat.lt location ir_byte_limit_v1)\n\
      (forward : @Eq (IROption IRByteFunctionV1) (ir_byte_function_v1 ctx fid) (@IROption.some IRByteFunctionV1 ({binding})))\n\
      (reverse : @Eq (IROption IRByteFunctionV1) (ir_byte_function_address_v1 ctx address) (@IROption.some IRByteFunctionV1 ({binding})))\n\
      (positive : Nat.lt 0 address) (bounded : Nat.lt address ir_byte_limit_v1)\n\
      (layout_found : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ({ty})) (@IROption.some IRByteLayoutV1 ({layout})))\n\
      (accessible : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) location 8 (ir_byte_effective_align_v1 align (ir_byte_layout_align_v1 ({layout})))) Bool.true) :\n{} :=\n\
      ir_byte_store_reload_eight_v1 ctx ({ty}) (IRScalar.ptr_ location) (IRScalar.fnptr_ fid) align mem ({layout}) location address\n\
        (ir_byte_function_lane_eight_v1 sig) layout_found (ir_byte_canonical_layout_eight_v1 ({ty}))\n\
        (ir_byte_pointer_address_bounded_v1 location location_bounded) accessible\n\
        (ir_byte_function_value_matches_of_catalog_v1 ctx fid sig address cc imported forward positive bounded)\n\
        (ir_byte_function_scalar_word_of_catalog_v1 ctx fid sig address cc imported forward reverse positive bounded)\n\
        (ir_byte_function_decode_word_of_catalog_v1 ctx fid sig address cc imported forward reverse positive bounded) bounded",
        eq(RESULT, actual, &expected))
}

impl Specification {
    /// Checked control/dispatch foundation, independently reusable by call
    /// proofs without installing concrete scalar specializations.
    pub(super) fn add_eval_ir_byte_access_rules_v1(&mut self) -> Result<(), SpecError> {
        self.add_byte_access_sources([
            CASE_TRUE.to_owned(),
            CASE_SOME.to_owned(),
            RELOAD.to_owned(),
            store_at_source(),
            load_at_source(),
            dispatch_source("store"),
            dispatch_source("load"),
            roundtrip_source(),
        ])
    }

    /// Install checked access laws after the byte prelude and function-catalog
    /// laws. The parent constructor owns that single ordered composition point.
    pub(super) fn add_eval_ir_byte_access_laws_v1(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_byte_access_rules_v1()?;
        let sources = [
            POINTER_ADDRESS.to_owned(),
            POINTER_FITS.to_owned(),
            POINTER_ENCODE.to_owned(),
            POINTER_DECODE.to_owned(),
            layout_eight_source(),
            lane_eight_source("u64", "IRTy.uint_ 64"),
            lane_eight_source("i64", "IRTy.int_ 64"),
            lane_eight_source("ptr", "IRTy.ptr_"),
            scalar_roundtrip_source(ScalarKind::U64),
            scalar_roundtrip_source(ScalarKind::I64),
            scalar_roundtrip_source(ScalarKind::Ptr),
            scalar_roundtrip_source(ScalarKind::Null),
            FUNCTION_LANE.to_owned(),
            function_roundtrip_source(),
        ];
        self.add_byte_access_sources(sources)
    }

    fn add_byte_access_sources(
        &mut self,
        sources: impl IntoIterator<Item = String>,
    ) -> Result<(), SpecError> {
        for source in sources {
            let name = source
                .split_whitespace()
                .nth(1)
                .unwrap_or("<unnamed access law>")
                .to_owned();
            self.add_recursive_def(&source, "Checked rule over actual public typed byte operations, with explicit admission premises")
                .map_err(|error| match error {
                    SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                    SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                    other => other,
                })?;
            self.verify_definition(&name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn spec() -> Specification {
        Specification::new_eval_ir_byte_prelude_spec_v1().unwrap()
    }
    fn checked(spec: &Specification, name: &str) {
        let declaration = spec.get_definition(name).expect("installed access law");
        assert!(!declaration.is_axiom && declaration.elaborated_value.is_some());
        spec.verify_definition(name).unwrap();
        let name = Name::from_string(name);
        assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
        assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
    }
    fn reject_type_mismatch(spec: &mut Specification, name: &str, source: &str) {
        let error = spec
            .add_recursive_def(source, "Adversarial typed access claim")
            .expect_err(name);
        crate::test_utils::assert_type_mismatch_rejection(&error, name);
        assert!(spec.get_definition(name).is_none());
    }

    #[test]
    fn actual_public_access_rules_are_checked() {
        crate::test_utils::run_with_stack(|| {
            let spec = spec();
            for name in [
                "ir_byte_case_true_v1",
                "ir_byte_case_some_v1",
                "ir_byte_reload_v1",
                "ir_byte_store_at_eight_rule_v1",
                "ir_byte_load_at_rule_v1",
                "ir_byte_store_dispatch_eight_v1",
                "ir_byte_load_dispatch_eight_v1",
                "ir_byte_store_reload_eight_v1",
                "ir_byte_pointer_address_bounded_v1",
                "ir_byte_pointer_value_fits_v1",
                "ir_byte_pointer_scalar_word_v1",
                "ir_byte_pointer_decode_word_v1",
                "ir_byte_canonical_layout_eight_v1",
                "ir_byte_u64_lane_eight_v1",
                "ir_byte_i64_lane_eight_v1",
                "ir_byte_ptr_lane_eight_v1",
                "ir_byte_u64_store_reload_v1",
                "ir_byte_i64_store_reload_v1",
                "ir_byte_ptr_store_reload_v1",
                "ir_byte_null_store_reload_v1",
                "ir_byte_function_lane_eight_v1",
                "ir_byte_fnptr_store_reload_v1",
            ] {
                checked(&spec, name);
            }
        });
    }

    #[test]
    fn typed_public_roundtrips_discharge_real_layout_and_alignment_checks() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            let mut layouts = "@IRList.nil IRByteLayoutV1".to_owned();
            for ty in ["IRTy.uint_ 64", "IRTy.int_ 64", "IRTy.ptr_"] {
                layouts = format!(
                    "@IRList.cons IRByteLayoutV1 ({}) ({layouts})",
                    canonical_layout(ty)
                );
            }
            let context = format!("def access_test_ctx : IRByteContextV1 := IRByteContextV1.mk\n\
              (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal)) ({layouts})\n\
              (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) (@IRList.nil IRByteSiteV1)");
            spec.add_recursive_def(
                &context,
                "Explicit logical test context, no installed image authority",
            )
            .unwrap();
            let mem = "IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 32 7 Bool.true) (@IRList.nil IRByteAllocationV1)) bytes 128";
            for (name, ty, location, align, parameters, value, word, argument, canonical) in [
                (
                    "u64",
                    "IRTy.uint_ 64",
                    16_u128,
                    0,
                    "(word : Nat)",
                    "IRScalar.int_ word",
                    "word",
                    "word",
                    format!("(bounded : Nat.lt word {LIMIT})"),
                ),
                (
                    "i64",
                    "IRTy.int_ 64",
                    17,
                    1,
                    "(word : Nat)",
                    "IRScalar.int_ word",
                    "word",
                    "word",
                    format!("(bounded : Nat.lt word {LIMIT})"),
                ),
                (
                    "ptr",
                    "IRTy.ptr_",
                    24,
                    8,
                    "(predecessor : Nat)",
                    "IRScalar.ptr_ (Nat.succ predecessor)",
                    "Nat.succ predecessor",
                    "predecessor",
                    format!("(bounded : Nat.lt (Nat.succ predecessor) {LIMIT})"),
                ),
                (
                    "null",
                    "IRTy.ptr_",
                    32,
                    0,
                    "",
                    "IRScalar.nullptr_",
                    "0",
                    "",
                    String::new(),
                ),
            ] {
                let bound_arg = if name == "null" { "" } else { "bounded" };
                let actual = format!("ir_byte_reload_v1 access_test_ctx ({ty}) (IRScalar.ptr_ {location}) {align}\n\
                    (ir_byte_store_v1 access_test_ctx ({ty}) (IRScalar.ptr_ {location}) ({value}) {align} Bool.false ({mem}))");
                let expected = result(value, &written(mem, &location.to_string(), word));
                let theorem_name = format!("access_test_{name}_universal_value");
                let source = format!("def {theorem_name} (bytes : Nat -> IROption Nat) {parameters} {canonical} :\n{} :=\n\
                    ir_byte_{name}_store_reload_v1 access_test_ctx {location} {align} ({mem}) {argument}\n\
                      (Nat.le_add_right {} {}) {bound_arg}\n\
                      (@Eq.refl (IROption IRByteLayoutV1) (@IROption.some IRByteLayoutV1 ({})))\n\
                      (@Eq.refl Bool Bool.true)", eq(RESULT, &actual, &expected), location+1, (1_u128<<64)-location-1, canonical_layout(ty));
                spec.add_recursive_def(
                    &source,
                    "Actual public accesses with arbitrary old bytes and symbolic scalar values",
                )
                .unwrap();
                checked(&spec, &theorem_name);
            }
        });
    }

    #[test]
    fn public_function_slot_preserves_identity_and_checks_load_signature() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            let layouts = format!("@IRList.cons IRByteLayoutV1 ({}) (@IRList.cons IRByteLayoutV1 ({}) (@IRList.nil IRByteLayoutV1))",
                canonical_layout("IRTy.func_ 17"), canonical_layout("IRTy.func_ 18"));
            // This is an exact catalog/layout fixture for public memory access,
            // not a claim that the empty module admits executing either function.
            spec.add_recursive_def(&format!("def access_function_ctx : IRByteContextV1 := IRByteContextV1.mk
              (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal)) ({layouts})
              (@IRList.nil IRByteSignatureV1)
              (@IRList.cons IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false)
                (@IRList.cons IRByteFunctionV1 (IRByteFunctionV1.mk 7 18 8192 1 Bool.false) (@IRList.nil IRByteFunctionV1)))
              (@IRList.nil IRByteSiteV1)"), "Exact sparse catalog and typed slot layouts, without module-execution authority").unwrap();
            let mem = "IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 8 7 Bool.true) (@IRList.nil IRByteAllocationV1)) bytes 128";
            let stored = format!("ir_byte_store_v1 access_function_ctx (IRTy.func_ 17) (IRScalar.ptr_ 16) (IRScalar.fnptr_ 41) 0 Bool.false ({mem})");
            let next = written(mem, "16", "4096");
            let actual = format!("ir_byte_reload_v1 access_function_ctx (IRTy.func_ 17) (IRScalar.ptr_ 16) 0 ({stored})");
            let expected = result("IRScalar.fnptr_ 41", &next);
            let proof = format!("ir_byte_fnptr_store_reload_v1 access_function_ctx 16 0 ({mem}) 41 17 4096 1 Bool.false
              (Nat.le_add_right 17 18446744073709551599)
              (@Eq.refl (IROption IRByteFunctionV1) (@IROption.some IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false)))
              (@Eq.refl (IROption IRByteFunctionV1) (@IROption.some IRByteFunctionV1 (IRByteFunctionV1.mk 41 17 4096 1 Bool.false)))
              (Nat.zero_lt_succ 4095) (Nat.le_add_right 4097 18446744073709547519)
              (@Eq.refl (IROption IRByteLayoutV1) (@IROption.some IRByteLayoutV1 ({})))
              (@Eq.refl Bool Bool.true)", canonical_layout("IRTy.func_ 17"));
            let source = format!(
                "def access_function_slot_identity (bytes : Nat -> IROption Nat) : {} := {proof}",
                eq(RESULT, &actual, &expected)
            );
            spec.add_recursive_def(&source, "Actual public store/load with arbitrary prior bytes, exact sparse function identity and signature").unwrap();
            checked(&spec, "access_function_slot_identity");

            reject_type_mismatch(
                &mut spec,
                "access_function_wrong_result",
                &format!(
                "def access_function_wrong_result (bytes : Nat -> IROption Nat) : {} := {proof}",
                eq(RESULT, &actual, &result("IRScalar.fnptr_ 7", &next))),
            );
            let wrong_type = format!("ir_byte_reload_v1 access_function_ctx (IRTy.func_ 18) (IRScalar.ptr_ 16) 0 ({stored})");
            let failure = fault("ub", "width_bounded", &next);
            spec.add_recursive_def(&format!("def access_function_wrong_signature_fault (bytes : Nat -> IROption Nat) : {} := {}",
                eq(RESULT, &wrong_type, &failure), refl(RESULT, &failure)),
                "Actual wrong-signature load faults and preserves the post-store memory").unwrap();
            checked(&spec, "access_function_wrong_signature_fault");
            reject_type_mismatch(&mut spec, "access_function_wrong_signature_success", &format!(
                "def access_function_wrong_signature_success (bytes : Nat -> IROption Nat) : {} := {proof}", eq(RESULT, &wrong_type, &expected)));
        });
    }

    #[test]
    fn typed_public_roundtrip_rejects_changed_guards_and_representations() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            let source = roundtrip_source();
            let (header, proof) = source.split_once(":=").unwrap();
            for (name, changed) in [
                (
                    "access_wrong_volatile",
                    header.replace("value align Bool.false mem", "value align Bool.true mem"),
                ),
                (
                    "access_wrong_lane",
                    header.replace("(@IROption.some Nat 8)", "(@IROption.some Nat 4)"),
                ),
                (
                    "access_missing_layout",
                    header.replace(
                        "(@IROption.some IRByteLayoutV1 layout)",
                        "(@IROption.none IRByteLayoutV1)",
                    ),
                ),
                (
                    "access_wrong_value",
                    header.replace(
                        "IRByteMemoryResultV1.value (value)",
                        "IRByteMemoryResultV1.value (IRScalar.unit_)",
                    ),
                ),
                (
                    "access_wrong_pointer",
                    header.replace(
                        "(ir_byte_pointer_address_v1 ptr) (@IROption.some Nat address)",
                        "(ir_byte_pointer_address_v1 ptr) (@IROption.none Nat)",
                    ),
                ),
                (
                    "access_wrong_extent",
                    header.replace(
                        "(ir_byte_mem_allocs_v1 mem) address 8 (ir_byte_effective_align_v1",
                        "(ir_byte_mem_allocs_v1 mem) address 4 (ir_byte_effective_align_v1",
                    ),
                ),
            ] {
                assert_ne!(
                    changed, header,
                    "mutation must alter its exact premise or endpoint"
                );
                let source = format!(
                    "{}:={proof}",
                    changed.replacen("ir_byte_store_reload_eight_v1", name, 1)
                );
                reject_type_mismatch(&mut spec, name, &source);
            }
            reject_type_mismatch(&mut spec, "access_zero_pointer_not_null",
                "def access_zero_pointer_not_null (ctx : IRByteContextV1) : @Eq (IROption IRScalar) (ir_byte_decode_word_v1 ctx IRTy.ptr_ 0) (@IROption.some IRScalar (IRScalar.ptr_ 0)) := @Eq.refl (IROption IRScalar) (@IROption.some IRScalar (IRScalar.ptr_ 0))");
            let u64_source = scalar_roundtrip_source(ScalarKind::U64);
            let (header, proof) = u64_source.split_once(":=").unwrap();
            let source = format!(
                "{}:={proof}",
                header
                    .replace(
                        "Nat.lt word 18446744073709551616",
                        "Nat.le word 18446744073709551616"
                    )
                    .replacen(
                        "ir_byte_u64_store_reload_v1",
                        "access_word_at_exclusive_bound",
                        1
                    )
            );
            reject_type_mismatch(&mut spec, "access_word_at_exclusive_bound", &source);
        });
    }
}
