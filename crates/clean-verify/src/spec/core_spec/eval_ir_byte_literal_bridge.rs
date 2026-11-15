// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One checked environment for the byte observer and existing literal model.
//! This is not an Arc/Name/Expr layout or production Rust execution theorem.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(crate) fn add_eval_ir_byte_literal_model_v1(&mut self) -> Result<(), SpecError> {
        crate::spec::decl_budget::with_spec_declaration_budget(|| {
            let previous = self.definitions().keys().cloned().collect();
            self.add_eval_ir_byte_literal_arithmetic_v1()?;
            self.add_eval_ir_byte_stages_v1()?;
            self.add_eval_ir_byte_literal_adapter_v1()?;
            self.add_eval_ir_byte_literal_typing_v1()?;
            self.verify_eval_ir_byte_additions_v1(&previous)
        })
    }

    // These five supplemental prelude lemmas are absent from the completed
    // Full environment. Reconstruct only their checked terms, over Full's
    // existing foundations; do not replace the environment or initialize the
    // whole prelude. They belong to the same audited delta as the byte model.
    fn add_eval_ir_byte_literal_arithmetic_v1(&mut self) -> Result<(), SpecError> {
        for source in [
            r"def Nat.le_add_left (a : Nat) (b : Nat) : Nat.le a (Nat.add b a) :=
Eq.subst Nat (fun (n : Nat) => Nat.le a n) (Nat.add a b) (Nat.add b a)
  (@Nat.add_comm a b) (@Nat.le_add_right a b)",
            r"def Nat.add_sub_cancel (a : Nat) (b : Nat) :
Eq Nat (Nat.sub (Nat.add a b) b) a :=
Nat.rec (fun (k : Nat) => Eq Nat (Nat.sub (Nat.add a k) k) a)
  (Eq.refl Nat a)
  (fun (k : Nat) (ih : Eq Nat (Nat.sub (Nat.add a k) k) a) =>
    Eq.trans Nat (Nat.sub (Nat.add a (Nat.succ k)) (Nat.succ k))
      (Nat.sub (Nat.add a k) k) a (nat_sub_succ_succ (Nat.add a k) k) ih) b",
            r"def Nat.ulpRound.le_of_add_le_add_right (a b k : Nat)
  (h : Nat.le (Nat.add a k) (Nat.add b k)) : Nat.le a b :=
Nat.rec (fun (n : Nat) => Nat.le (Nat.add a n) (Nat.add b n) -> Nat.le a b)
  (fun (base : Nat.le a b) => base)
  (fun (n : Nat)
    (ih : Nat.le (Nat.add a n) (Nat.add b n) -> Nat.le a b)
    (step : Nat.le (Nat.add a (Nat.succ n)) (Nat.add b (Nat.succ n))) =>
    ih (@Nat.le_of_succ_le_succ (Nat.add a n) (Nat.add b n) step)) k h",
            r"def Nat.add_left_cancel (a b c : Nat)
  (h : Eq Nat (Nat.add a b) (Nat.add a c)) : Eq Nat b c :=
let swapped : Eq Nat (Nat.add b a) (Nat.add c a) :=
  Eq.trans Nat (Nat.add b a) (Nat.add a b) (Nat.add c a) (@Nat.add_comm b a)
    (Eq.trans Nat (Nat.add a b) (Nat.add a c) (Nat.add c a) h (@Nat.add_comm a c));
Eq.trans Nat b (Nat.sub (Nat.add b a) a) c
  (Eq.symm Nat (Nat.sub (Nat.add b a) a) b (Nat.add_sub_cancel b a))
  (Eq.trans Nat (Nat.sub (Nat.add b a) a) (Nat.sub (Nat.add c a) a) c
    (Eq.cong Nat Nat (fun (n : Nat) => Nat.sub n a) (Nat.add b a) (Nat.add c a) swapped)
    (Nat.add_sub_cancel c a))",
            r"def Nat.right_distrib (a b c : Nat) :
Eq Nat (Nat.mul (Nat.add a b) c) (Nat.add (Nat.mul a c) (Nat.mul b c)) :=
Eq.trans Nat (Nat.mul (Nat.add a b) c) (Nat.mul c (Nat.add a b))
  (Nat.add (Nat.mul a c) (Nat.mul b c)) (@Nat.mul_comm (Nat.add a b) c)
  (Eq.trans Nat (Nat.mul c (Nat.add a b)) (Nat.add (Nat.mul c a) (Nat.mul c b))
    (Nat.add (Nat.mul a c) (Nat.mul b c)) (@Nat.left_distrib c a b)
    (Eq.trans Nat (Nat.add (Nat.mul c a) (Nat.mul c b))
      (Nat.add (Nat.mul a c) (Nat.mul c b)) (Nat.add (Nat.mul a c) (Nat.mul b c))
      (Eq.cong Nat Nat (fun (n : Nat) => Nat.add n (Nat.mul c b))
        (Nat.mul c a) (Nat.mul a c) (@Nat.mul_comm c a))
      (Eq.cong Nat Nat (fun (n : Nat) => Nat.add (Nat.mul a c) n)
        (Nat.mul c b) (Nat.mul b c) (@Nat.mul_comm c b))))",
        ] {
            self.add_recursive_def(source, "Constructive supplemental Nat lemma for Full/Byte coexistence; preserves the existing Full foundations and is included in the empty-closure audit.")?;
        }
        Ok(())
    }

    fn add_eval_ir_byte_literal_adapter_v1(&mut self) -> Result<(), SpecError> {
        for source in [
            r"def ir_byte_builtin_literal_type_v1 (atom : IRBuiltinNameAtomV1) : KExpr :=
match atom with
| IRBuiltinNameAtomV1.nat_ => literal_nat_type
| IRBuiltinNameAtomV1.string_ => literal_string_type",
            r"def ir_byte_literal_type_result_v1
  (result : IROption IRBuiltinNameAtomV1) : IROption KExpr :=
IROption.rec IRBuiltinNameAtomV1
  (fun (_ : IROption IRBuiltinNameAtomV1) => IROption KExpr)
  (IROption.none KExpr)
  (fun (atom : IRBuiltinNameAtomV1) =>
    IROption.some KExpr (ir_byte_builtin_literal_type_v1 atom)) result",
            r"def ir_byte_literal_type_v1 (mem : IRByteMemoryV1)
  (declaredTy : IRTy) (value : IRScalar) : IROption KExpr :=
ir_byte_literal_type_result_v1 (ir_byte_builtin_name_atom_v1 mem declaredTy value)",
        ] {
            self.add_recursive_def(
                source,
                "Exact builtin byte atoms mapped to the existing reflection-owned literal type aliases in the same checked model environment; not a Rust layout or execution relation.",
            )?;
        }
        for (kind, bytes) in [("nat", b"Nat".as_slice()), ("string", b"String".as_slice())] {
            let length = bytes.len();
            let mut address = "data".to_owned();
            let mut premises = String::new();
            let mut arguments = String::new();
            for (index, byte) in bytes.iter().enumerate() {
                premises.push_str(&format!(
                    "\n  (byte{index} : Eq (IROption Nat) (bytes ({address})) (IROption.some Nat {byte}))"
                ));
                arguments.push_str(&format!(" byte{index}"));
                address = format!("Nat.succ ({address})");
            }
            self.add_recursive_def(
                &format!("def ir_byte_literal_{kind}_input_v1
  (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (next data : Nat) (bounded : Nat.lt data ir_byte_limit_v1)
  (access : Eq Bool (ir_byte_accessible_v1 allocs data {length} 1) Bool.true)
  {premises} :
Eq (IROption KExpr)
  (ir_byte_literal_type_v1 (IRByteMemoryV1.mk allocs bytes next)
    IRTy.fatstr_ (IRScalar.fat_ data {length}))
  (IROption.some KExpr literal_{kind}_type) :=
ir_eq_cong (IROption IRBuiltinNameAtomV1) (IROption KExpr)
  ir_byte_literal_type_result_v1
  (ir_byte_builtin_name_atom_v1 (IRByteMemoryV1.mk allocs bytes next)
    IRTy.fatstr_ (IRScalar.fat_ data {length}))
  (IROption.some IRBuiltinNameAtomV1 IRBuiltinNameAtomV1.{kind}_)
  (ir_byte_builtin_{kind}_input_v1 allocs bytes next data bounded access {arguments})"),
                "Existing literal-model type derived from the actual accessible initialized builtin-name bytes, not assumed decoder output. Reflection tags are never copied or hardcoded.",
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_literal_bridge_tests.rs"]
mod tests;
