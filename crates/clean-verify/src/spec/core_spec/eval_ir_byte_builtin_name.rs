// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact builtin-name atoms from an already projected string view.
//!
//! This observer requires initialized ASCII bytes in one live accessible
//! allocation. It does not decode Arc/Name/Expr layouts, execute Rust, or admit
//! aggregate/fat-pointer memory operations. In particular, a ContainerLen data
//! pointer is NOT the string tail of an Arc allocation. A source attachment
//! must establish that projection from captured layout facts separately.

use crate::spec::{SpecError, Specification};

const ATOM: &str = "IRBuiltinNameAtomV1";
const OPTION: &str = "IROption IRBuiltinNameAtomV1";
const NONE: &str = "@IROption.none IRBuiltinNameAtomV1";
const NAMES: [(&str, &[u8]); 2] = [("nat", b"Nat"), ("string", b"String")];

fn word(bytes: &[u8]) -> u64 {
    bytes
        .iter()
        .rev()
        .fold(0, |tail, byte| u64::from(*byte) + 256 * tail)
}

fn address(offset: usize) -> String {
    (0..offset).fold("data".to_owned(), |base, _| format!("(Nat.succ {base})"))
}

fn guard(length: usize) -> String {
    format!(
        "Bool.and (ir_byte_fat_value_matches_v1 IRTy.fatstr_ data {length})
      (ir_byte_accessible_v1 allocs data {length} 1)"
    )
}

/// The observer's fixed-width branch, with its read result left abstract.
fn observed_read(name: &str, bytes: &[u8], read: &str) -> String {
    format!(
        "@Bool.rec (fun (_ : Bool) => {OPTION}) ({NONE})
      (ir_byte_builtin_name_word_v1 {} {ATOM}.{name}_ ({read})) ({})",
        word(bytes),
        guard(bytes.len())
    )
}

impl Specification {
    pub(super) fn add_eval_ir_byte_builtin_name_v1(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive IRBuiltinNameAtomV1 : Type\n| nat_ : IRBuiltinNameAtomV1\n| string_ : IRBuiltinNameAtomV1",
            "Distinct exact builtin string atoms, not model Name identifiers or Rust enum/layout tags.",
        )?;
        self.add_recursive_def(
            &format!("def ir_byte_builtin_name_word_v1 (expected : Nat) (atom : {ATOM})
  (read : IROption Nat) : {OPTION} :=
@IROption.rec Nat (fun (_ : IROption Nat) => {OPTION}) ({NONE})
  (fun (actual : Nat) => @Bool.rec (fun (_ : Bool) => {OPTION}) ({NONE})
    (@IROption.some {ATOM} atom) (ir_nat_eqb actual expected)) read"),
            "Exact initialized-word comparison behind the public observer's fixed ASCII/length selection; no standalone string validity claim.",
        )?;
        let branch = |name: &str, bytes: &[u8]| {
            format!(
                "ir_byte_builtin_name_word_v1 {} {ATOM}.{name}_
  (ir_byte_read_word_v1 bytes {} data)",
                word(bytes),
                bytes.len()
            )
        };
        self.add_recursive_def(
            &format!("def ir_byte_builtin_name_bytes_v1 (bytes : Nat -> IROption Nat)
  (data length : Nat) : {OPTION} :=
@Bool.rec (fun (_ : Bool) => {OPTION})
  (@Bool.rec (fun (_ : Bool) => {OPTION}) ({NONE}) ({}) (ir_nat_eqb length 6))
  ({}) (ir_nat_eqb length 3)", branch("string", b"String"), branch("nat", b"Nat")),
            "Only three or six initialized bytes can be observed; ASCII Nat and String are distinct and exact, including case and length.",
        )?;
        self.add_recursive_def(
            &format!("def ir_byte_builtin_name_at_v1 (allocs : IRList IRByteAllocationV1)
  (bytes : Nat -> IROption Nat) (data length : Nat) : {OPTION} :=
@Bool.rec (fun (_ : Bool) => {OPTION}) ({NONE})
  (ir_byte_builtin_name_bytes_v1 bytes data length)
  (Bool.and (ir_byte_fat_value_matches_v1 IRTy.fatstr_ data length)
    (ir_byte_accessible_v1 allocs data length 1))"),
            "Canonical LE64 words, non-null bounds, unique live allocation and initialized exact bytes; no rights inferred from a fat carrier alone.",
        )?;
        self.add_recursive_def(
            &format!("def ir_byte_builtin_name_atom_v1 (mem : IRByteMemoryV1)
  (declaredTy : IRTy) (value : IRScalar) : {OPTION} :=
match declaredTy with
| IRTy.fatstr_ => match value with
  | IRScalar.fat_ data length => ir_byte_builtin_name_at_v1
      (ir_byte_mem_allocs_v1 mem) (ir_byte_mem_bytes_v1 mem) data length
  | _ => {NONE}
| _ => {NONE}"),
            "Exact builtin-name observer for an already projected FatStr view. Other nominal fat kinds, including ContainerLen, are refused; no Rust heap-layout or execution theorem.",
        )?;
        for (name, bytes) in NAMES {
            self.add_builtin_name_laws_v1(name, bytes)?;
        }
        Ok(())
    }

    fn add_builtin_name_laws_v1(&mut self, name: &str, bytes: &[u8]) -> Result<(), SpecError> {
        let length = bytes.len();
        let expected_word = word(bytes);
        let atom = format!("@IROption.some {ATOM} {ATOM}.{name}_");
        let byte_premises = bytes
            .iter()
            .enumerate()
            .map(|(i, byte)| {
                format!(
                    "\n  (byte{i} : @Eq (IROption Nat) (bytes {}) (@IROption.some Nat {byte}))",
                    address(i)
                )
            })
            .collect::<String>();
        let mut read_proof = format!("ir_byte_read_zero_v1 bytes {}", address(length));
        for (i, byte) in bytes.iter().enumerate().rev() {
            let rest = word(&bytes[i + 1..]);
            let read_step = format!(
                "ir_byte_read_success_v1 bytes {} {} {byte} {}
  byte{i} (@Eq.refl Bool Bool.true) ({read_proof})",
                length - i - 1,
                address(i),
                rest
            );
            // The reflected Nat.mul recurses on its SECOND operand. Never
            // ask independent replay to normalize 256 * a packed string tail
            // (hundreds of billions of recursive steps). Transport by the
            // already checked commutativity theorem, then normalize at most
            // 256 steps. The reader, input premises and numeric endpoint stay
            // unchanged; this is a proof repair, not an evaluator substitution.
            read_proof = format!(
                "@Eq.trans (IROption Nat)
  (ir_byte_read_word_v1 bytes {} {})
  (@IROption.some Nat (Nat.add {byte} (Nat.mul 256 {rest})))
  (@IROption.some Nat {}) ({read_step})
  (ir_eq_cong Nat (IROption Nat)
    (fun (product : Nat) => @IROption.some Nat (Nat.add {byte} product))
    (Nat.mul 256 {rest}) (Nat.mul {rest} 256) (Nat.mul_comm 256 {rest}))",
                length - i,
                address(i),
                word(&bytes[i..])
            );
        }
        self.add_recursive_def(
            &format!("def ir_byte_builtin_{name}_read_v1 (bytes : Nat -> IROption Nat)
  (data : Nat) {byte_premises} :
  @Eq (IROption Nat) (ir_byte_read_word_v1 bytes {length} data)
    (@IROption.some Nat {expected_word}) :=\n{read_proof}"),
            "Exact little-endian reader result derived from each initialized ASCII input byte; no desired decoder result premise.",
        )?;
        let read = format!("ir_byte_read_word_v1 bytes {length} data");
        let byte_args = (0..length).map(|i| format!(" byte{i}")).collect::<String>();
        let decoded_read =
            format!("ir_byte_builtin_name_word_v1 {expected_word} {ATOM}.{name}_ ({read})");
        let decoded_proof = format!(
            "ir_eq_cong (IROption Nat) ({OPTION})
  (ir_byte_builtin_name_word_v1 {expected_word} {ATOM}.{name}_)
  ({read}) (@IROption.some Nat {expected_word})
  (ir_byte_builtin_{name}_read_v1 bytes data {byte_args})"
        );
        let fits = format!(
            "ir_byte_function_and_true_v1
  (ir_nat_ltb data ir_byte_limit_v1) (ir_nat_ltb {length} ir_byte_limit_v1)
  (ir_byte_ltb_of_lt_v1 data ir_byte_limit_v1 bounded) (@Eq.refl Bool Bool.true)"
        );
        self.add_recursive_def(
            &format!("def ir_byte_builtin_{name}_input_v1
  (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (next data : Nat) (bounded : Nat.lt data ir_byte_limit_v1)
  (access : @Eq Bool (ir_byte_accessible_v1 allocs data {length} 1) Bool.true)
  {byte_premises} :
  @Eq ({OPTION}) (ir_byte_builtin_name_atom_v1 (IRByteMemoryV1.mk allocs bytes next)
    IRTy.fatstr_ (IRScalar.fat_ data {length})) ({atom}) :=
ir_byte_case_true_v1 ({OPTION}) ({}) ({NONE}) ({decoded_read}) ({atom})
  (ir_byte_function_and_true_v1 (ir_byte_fat_value_matches_v1 IRTy.fatstr_ data {length})
    (ir_byte_accessible_v1 allocs data {length} 1) ({fits}) access)
  ({decoded_proof})", guard(length)),
            "Public decoder success derived from canonical input data, actual allocation accessibility and every initialized ASCII byte. Memory cursor and all other bytes remain arbitrary.",
        )?;

        let mem = |bytes: &str, next: &str| format!("IRByteMemoryV1.mk allocs ({bytes}) {next}");
        let decode = |memory: &str| {
            format!("ir_byte_builtin_name_atom_v1 ({memory}) IRTy.fatstr_ (IRScalar.fat_ data {length})")
        };
        let lhs = decode(&mem("left", "leftNext"));
        let rhs = decode(&mem("right", "rightNext"));
        self.add_recursive_def(
            &format!("def ir_byte_builtin_{name}_range_frame_v1
  (allocs : IRList IRByteAllocationV1) (left right : Nat -> IROption Nat)
  (leftNext rightNext data : Nat)
  (same : forall (offset : Nat), Nat.lt offset {length} ->
    @Eq (IROption Nat) (left (Nat.add data offset)) (right (Nat.add data offset))) :
  @Eq ({OPTION}) ({lhs}) ({rhs}) :=
ir_eq_cong (IROption Nat) ({OPTION}) (fun (read : IROption Nat) => {})
  (ir_byte_read_word_v1 left {length} data) (ir_byte_read_word_v1 right {length} data)
  (ir_byte_read_range_congr_v1 left right {length} data same)", observed_read(name, bytes, "read")),
            "Range-local observer framing, including failed decodes and undefined bytes. Same allocation ledger, arbitrary distinct memory cursors; no function extensionality.",
        )?;
        for clear in [false, true] {
            let (operation, parameter, write, point) = if clear {
                (
                    "clear",
                    "",
                    "ir_byte_clear_v1 bytes writeBase writeSize".to_owned(),
                    "ir_byte_clear_outside_v1 bytes writeBase writeSize (Nat.add data offset)"
                        .to_owned(),
                )
            } else {
                (
                    "write",
                    "(word : Nat)",
                    "ir_byte_write_word_v1 bytes writeBase writeSize word".to_owned(),
                    "ir_byte_write_outside_v1 bytes writeBase writeSize word (Nat.add data offset)"
                        .to_owned(),
                )
            };
            self.add_recursive_def(
                &format!("def ir_byte_builtin_{name}_{operation}_frame_v1
  (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (next data writeBase writeSize : Nat) {parameter}
  (apart : Or (Nat.le (Nat.add data {length}) writeBase)
    (Nat.le (Nat.add writeBase writeSize) data)) :
  @Eq ({OPTION}) ({}) ({}) :=
ir_byte_builtin_{name}_range_frame_v1 allocs ({write}) bytes next next data
  (fun (offset : Nat) (inside : Nat.lt offset {length}) =>
    {point} (ir_byte_disjoint_range_point_v1 data {length} writeBase writeSize offset apart inside))",
                    decode(&mem(&write, "next")), decode(&mem("bytes", "next"))),
                "Disjoint byte write/clear preserves this exact observer result through range-local framing, without assuming decoding succeeds.",
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_builtin_name_tests.rs"]
mod tests;
