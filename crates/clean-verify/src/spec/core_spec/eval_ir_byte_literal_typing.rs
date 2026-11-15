// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Input-derived byte observations composed with the existing literal judgments.
//!
//! These are model-to-model terms, not a Rust heap representation or execution
//! theorem. The input payload is a model natural/string identity, not a decoded
//! production Literal. The builtin-name bytes determine the observed result;
//! no premise supplies that result. Rejection has type Empty, with no default
//! KExpr. Declarative typing follows exact inference and makes no claim that
//! arbitrary environments cannot convert the two builtin types.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_literal_typing_v1(&mut self) -> Result<(), SpecError> {
        for (name, judgment) in [("infers", "KernelInfers"), ("typing", "TypingCtxConv")] {
            self.add_recursive_def(
                &format!(
                    "def ir_byte_literal_{name}_v1 (tenv : KDeclEnv)
  (G : ListType KExpr) (input : KExpr) (result : IROption KExpr) : Type :=
IROption.rec KExpr (fun (_ : IROption KExpr) => Type) Empty
  (fun (T : KExpr) => {judgment} tenv G input T) result"
                ),
                "Lift the existing model judgment over the actual optional observation: rejection is Empty and a successful value is the judgment's exact result type. No source execution or fallback type is asserted.",
            )?;
        }
        self.add_recursive_def(
            r"def ir_byte_literal_infers_sound_v1 (tenv : KDeclEnv)
  (G : ListType KExpr) (input : KExpr) (result : IROption KExpr) :
  ir_byte_literal_infers_v1 tenv G input result ->
  ir_byte_literal_typing_v1 tenv G input result :=
IROption.rec KExpr
  (fun (observed : IROption KExpr) =>
    ir_byte_literal_infers_v1 tenv G input observed ->
    ir_byte_literal_typing_v1 tenv G input observed)
  (fun (rejected : Empty) => rejected)
  (fun (T : KExpr) (inferred : KernelInfers tenv G input T) =>
    kernel_infers_sound tenv G input T inferred) result",
            "Constructive option-lift of the existing algorithmic-to-declarative model theorem. The same observed result is retained; the rejection branch does not manufacture acceptance.",
        )?;

        for (kind, bytes) in [("nat", b"Nat".as_slice()), ("string", b"String".as_slice())] {
            let length = bytes.len();
            let mut address = "data".to_owned();
            let mut premises = String::new();
            let mut byte_arguments = String::new();
            for (index, byte) in bytes.iter().enumerate() {
                premises.push_str(&format!(
                    "\n  (byte{index} : Eq (IROption Nat) (bytes ({address})) (IROption.some Nat {byte}))"
                ));
                byte_arguments.push_str(&format!(" byte{index}"));
                address = format!("Nat.succ ({address})");
            }
            let telescope = format!(
                "(tenv : KDeclEnv) (G : ListType KExpr) (payload : Nat)
  (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (next data : Nat) (bounded : Nat.lt data ir_byte_limit_v1)
  (access : Eq Bool (ir_byte_accessible_v1 allocs data {length} 1) Bool.true)
  {premises}"
            );
            let observed = format!(
                "ir_byte_literal_type_v1 (IRByteMemoryV1.mk allocs bytes next)
    IRTy.fatstr_ (IRScalar.fat_ data {length})"
            );
            let expected = format!("IROption.some KExpr literal_{kind}_type");
            let arguments = format!("allocs bytes next data bounded access {byte_arguments}");

            self.add_recursive_def(
                &format!(
                    "def ir_byte_literal_{kind}_infers_input_v1 {telescope} :
  ir_byte_literal_infers_v1 tenv G (literal_{kind} payload) ({observed}) :=
Eq.substType (IROption KExpr)
  (fun (result : IROption KExpr) =>
    ir_byte_literal_infers_v1 tenv G (literal_{kind} payload) result)
  ({expected}) ({observed})
  (Eq.symm (IROption KExpr) ({observed}) ({expected})
    (ir_byte_literal_{kind}_input_v1 {arguments}))
  (KernelInfers.lit_{kind} tenv G payload)"
                ),
                "Exact existing literal inference transported along the input-derived byte observer equation. Premises are only the canonical address bound, live accessibility and initialized bytes; the model payload/environment/context are arbitrary.",
            )?;
            self.add_recursive_def(
                &format!(
                    "def ir_byte_literal_{kind}_typing_input_v1 {telescope} :
  ir_byte_literal_typing_v1 tenv G (literal_{kind} payload) ({observed}) :=
ir_byte_literal_infers_sound_v1 tenv G (literal_{kind} payload) ({observed})
  (ir_byte_literal_{kind}_infers_input_v1 tenv G payload {arguments})"
                ),
                "The input-derived exact inference composed with kernel_infers_sound. This is declarative model acceptance, not production Rust acceptance or arbitrary-environment non-convertibility of builtin types.",
            )?;
        }
        Ok(())
    }
}
