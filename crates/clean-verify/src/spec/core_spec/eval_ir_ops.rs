// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — value-level evaluators (job **C3**).
//!
//! Everything here is a pure function from [`IRScalar`] operands to an
//! `IRStepResult`; nothing touches the machine. The machine transitions and
//! the 28-arm instruction dispatch live in [`super::eval_ir_machine`].
//!
//! Every operator alphabet is dispatched **exhaustively** — 20 `IRBinOp`, 9
//! `IRUnOp`, 10 `IRICmpOp`, 12 `IRFCmpOp`, 17 `IRCastOp`. Arms outside the
//! modelled fragment return a tagged [`IROutcome.unmodelled`], never a value;
//! the complete list is in [`super::eval_ir_state`]'s docs.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Register the value-level evaluators.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_ops(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_coercions()?;
        self.add_eval_ir_arith()?;
        self.add_eval_ir_compare()?;
        self.add_eval_ir_cast()
    }

    /// Partial coercions out of the value domain, plus the argument-shape
    /// combinators every arithmetic arm is written through.
    fn add_eval_ir_coercions(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def ir_as_int (v : IRScalar) : IROption Nat := match v with
| IRScalar.undef_ => IROption.none Nat
| IRScalar.bool_ b => IROption.none Nat
| IRScalar.int_ n => IROption.some Nat n
| IRScalar.float_ n => IROption.none Nat
| IRScalar.unit_ => IROption.none Nat
| IRScalar.ptr_ a => IROption.none Nat
| IRScalar.nullptr_ => IROption.none Nat
| IRScalar.fat_ d md => IROption.none Nat
| IRScalar.fnptr_ f => IROption.none Nat
| IRScalar.aggv sp => IROption.none Nat
| IRScalar.vnil => IROption.none Nat
| IRScalar.vcons x rest => IROption.none Nat",
            "Integer view of a value. A pointer is deliberately NOT an integer: reading an \
             address as a number requires an explicit Cast ptrtoint, exactly as in trust-ir.",
        )?;

        self.add_recursive_def(
            r"def ir_as_bool (v : IRScalar) : IROption Bool := match v with
| IRScalar.undef_ => IROption.none Bool
| IRScalar.bool_ b => IROption.some Bool b
| IRScalar.int_ n => IROption.none Bool
| IRScalar.float_ n => IROption.none Bool
| IRScalar.unit_ => IROption.none Bool
| IRScalar.ptr_ a => IROption.none Bool
| IRScalar.nullptr_ => IROption.none Bool
| IRScalar.fat_ d md => IROption.none Bool
| IRScalar.fnptr_ f => IROption.none Bool
| IRScalar.aggv sp => IROption.none Bool
| IRScalar.vnil => IROption.none Bool
| IRScalar.vcons x rest => IROption.none Bool",
            "Boolean view of a value. i1 is a genuine Bool here, not an integer of width one.",
        )?;

        // The comparison key. Two values of the COMPARABLE constructors are
        // equal iff their tag and their payload code agree. Splitting equality
        // into (tag, code) avoids a twelve-by-twelve constructor cross-product while
        // deciding exactly the same relation: distinct constructors get
        // distinct tags, so `int_ 3` and `ptr_ 3` compare unequal, and
        // `nullptr_` is unequal to every `ptr_ a` including a = 0.
        self.add_recursive_def(
            r"def ir_scalar_tag (v : IRScalar) : Nat := match v with
| IRScalar.undef_ => Nat.zero
| IRScalar.bool_ b => Nat.succ Nat.zero
| IRScalar.int_ n => Nat.succ (Nat.succ Nat.zero)
| IRScalar.float_ n => Nat.succ (Nat.succ (Nat.succ Nat.zero))
| IRScalar.unit_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRScalar.ptr_ a => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
| IRScalar.nullptr_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
| IRScalar.fat_ d md => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
| IRScalar.fnptr_ f => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))
| IRScalar.aggv sp => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))
| IRScalar.vnil => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))
| IRScalar.vcons x rest => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))))",
            "Constructor tag of a value, for the equality decision. Injective on constructors.",
        )?;

        self.add_recursive_def(
            r"def ir_scalar_code (v : IRScalar) : Nat := match v with
| IRScalar.undef_ => Nat.zero
| IRScalar.bool_ b => Bool.rec (fun (_ : Bool) => Nat) Nat.zero (Nat.succ Nat.zero) b
| IRScalar.int_ n => n
| IRScalar.float_ n => n
| IRScalar.unit_ => Nat.zero
| IRScalar.ptr_ a => a
| IRScalar.nullptr_ => Nat.zero
| IRScalar.fat_ d md => d
| IRScalar.fnptr_ f => f
| IRScalar.aggv sp => Nat.zero
| IRScalar.vnil => Nat.zero
| IRScalar.vcons x rest => Nat.zero",
            "Payload code of a value, for the equality decision. Only consulted for the \
             comparable constructors (see ir_scalar_cmpable), where it is faithful: Bool maps \
             false to 0 and true to 1, and the payload-free constructors map to 0. The \
             aggregate and spine constructors map to 0, which is never observed: `ir_eqb` \
             consults `code` only when both operands are `cmpable`, and none of them is.",
        )?;

        self.add_recursive_def(
            r"def ir_scalar_cmpable (v : IRScalar) : Bool := match v with
| IRScalar.undef_ => Bool.false
| IRScalar.bool_ b => Bool.true
| IRScalar.int_ n => Bool.true
| IRScalar.float_ n => Bool.false
| IRScalar.unit_ => Bool.true
| IRScalar.ptr_ a => Bool.true
| IRScalar.nullptr_ => Bool.true
| IRScalar.fat_ d md => Bool.false
| IRScalar.fnptr_ f => Bool.true
| IRScalar.aggv sp => Bool.false
| IRScalar.vnil => Bool.false
| IRScalar.vcons x rest => Bool.false",
            "Which values ICmp eq/ne may be decided on. `undef_` is excluded because comparing \
             an undefined value has no answer; `float_` because there is no float domain; \
             `fat_` because wide-pointer equality also compares metadata, which the (data, meta) \
             pair would have to decide jointly; `aggv` and the bare spine constructors because \
             structural aggregate equality is decidable here but deliberately out of scope — \
             `ir_scalar_code` is a single `Nat` and cannot summarize a tree, so deciding them \
             would need a separate recursive `ir_value_eqb`. ICmp on aggregates therefore \
             remains `type_error not_bool`.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_eqb (a : IRScalar) (b : IRScalar) : IROption Bool := ",
                "Bool.rec (fun (_ : Bool) => IROption Bool) ",
                "(IROption.none Bool) ",
                "(IROption.some Bool (Bool.and (ir_nat_eqb (ir_scalar_tag a) (ir_scalar_tag b)) ",
                "(ir_nat_eqb (ir_scalar_code a) (ir_scalar_code b)))) ",
                "(Bool.and (ir_scalar_cmpable a) (ir_scalar_cmpable b))",
            ),
            "Decidable equality on the comparable fragment of the value domain; none where the \
             comparison has no defined answer. Bool.rec minor order is (false, true).",
        )?;

        // Argument-shape combinators. Every arithmetic arm below is one
        // application of one of these, which is what keeps the 20/9/10/17-arm
        // dispatches flat.
        self.add_recursive_def(
            concat!(
                "def ir_int2 (f : Nat -> Nat -> IRStepResult) (a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (x : Nat) => IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (y : Nat) => f x y) (ir_as_int b)) ",
                "(ir_as_int a)",
            ),
            "Apply a binary integer operation, faulting with type_error not_int unless both \
             operands are integers.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_int1 (f : Nat -> IRStepResult) (a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (x : Nat) => f x) (ir_as_int a)",
            ),
            "Apply a unary integer operation, faulting with type_error not_int otherwise.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_bitop (f : Bool -> Bool -> Bool) (a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.unmodelled IRFault.bitlevel)) ",
                "(fun (x : Bool) => IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.unmodelled IRFault.bitlevel)) ",
                "(fun (y : Bool) => IRStepResult.value (IRScalar.bool_ (f x y))) (ir_as_bool b)) ",
                "(ir_as_bool a)",
            ),
            "Apply And/Or/Xor at the i1 width the lowerer emits for logical operators. On \
             INTEGER operands the result is the tagged `unmodelled bitlevel` outcome, not a \
             wrong number: the Nat value domain has no bit-level view.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_bool_result (o : IROption Bool) : IRStepResult := ",
                "IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (x : Bool) => IRStepResult.value (IRScalar.bool_ x)) o",
            ),
            "Lift a decided boolean into a step result.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_bool_result_neg (o : IROption Bool) : IRStepResult := ",
                "IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (x : Bool) => IRStepResult.value (IRScalar.bool_ (Bool.not x))) o",
            ),
            "Lift the negation of a decided boolean into a step result (the ne_ arm of ICmp).",
        )?;

        self.add_recursive_def(
            r"def ir_ty_int_width (t : IRTy) : IROption Nat := match t with
| IRTy.bool_ => IROption.none Nat
| IRTy.int_ w => IROption.some Nat w
| IRTy.uint_ w => IROption.some Nat w
| IRTy.float_ w => IROption.none Nat
| IRTy.ptr_ => IROption.none Nat
| IRTy.ref_ p => IROption.none Nat
| IRTy.refmut_ p => IROption.none Nat
| IRTy.rawconst_ p => IROption.none Nat
| IRTy.rawmut_ p => IROption.none Nat
| IRTy.rc_ p => IROption.none Nat
| IRTy.fatptr_ p => IROption.none Nat
| IRTy.unit_ => IROption.none Nat
| IRTy.never_ => IROption.none Nat
| IRTy.tuple_ n => IROption.none Nat
| IRTy.array_ e n => IROption.none Nat
| IRTy.struct_ n => IROption.none Nat
| IRTy.enum_ n => IROption.none Nat
| IRTy.func_ n => IROption.none Nat",
            "Return the bit width of a signed or unsigned machine-integer type. Every other type \
             is rejected rather than silently receiving Nat arithmetic.",
        )?;

        self.add_recursive_def(
            r"def ir_const_value (c : IRConst) : IRScalar := match c with
| IRConst.int_ n => IRScalar.int_ n
| IRConst.bool_ b => IRScalar.bool_ b
| IRConst.unit_ => IRScalar.unit_
| IRConst.null_ => IRScalar.nullptr_
| IRConst.undef_ => IRScalar.undef_
| IRConst.float_ n => IRScalar.float_ n
| IRConst.func_ f => IRScalar.fnptr_ f",
            "Materialize a constant as a value. Total: every IRConst constructor has a value.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_const_int_eval (t : IRTy) (n : Nat) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (w : Nat) => IRStepResult.value (IRScalar.int_ (ir_wrap w n))) ",
                "(ir_ty_int_width t)",
            ),
            "Materialize an integer constant at its declared machine width. The stored Nat is a \
             bit-pattern carrier, so out-of-range literals are reduced to the canonical residue.",
        )?;

        self.add_recursive_def(
            r"def ir_const_eval (t : IRTy) (c : IRConst) : IRStepResult := match c with
| IRConst.int_ n => ir_const_int_eval t n
| IRConst.bool_ b => IRStepResult.value (IRScalar.bool_ b)
| IRConst.unit_ => IRStepResult.value IRScalar.unit_
| IRConst.null_ => IRStepResult.value IRScalar.nullptr_
| IRConst.undef_ => IRStepResult.value IRScalar.undef_
| IRConst.float_ n => IRStepResult.value (IRScalar.float_ n)
| IRConst.func_ f => IRStepResult.value (IRScalar.fnptr_ f)",
            "The Const instruction's typed evaluator. Integer constants are canonicalized modulo \
             2^w; every other constant retains its exact value-domain constructor.",
        )?;

        Ok(())
    }

    /// BinOp (20/20) and UnOp (9/9).
    fn add_eval_ir_arith(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_div_checked (x : Nat) (y : Nat) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.value (IRScalar.int_ (ir_nat_div x y))) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.div_zero)) ",
                "(ir_nat_eqb y Nat.zero)",
            ),
            "Division with the division-by-zero UB check the real instruction has.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_rem_checked (x : Nat) (y : Nat) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.value (IRScalar.int_ (ir_nat_rem x y))) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.div_zero)) ",
                "(ir_nat_eqb y Nat.zero)",
            ),
            "Remainder with the same zero-divisor UB check.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_float_fault : IRStepResult := ",
                "IRStepResult.fault (IROutcome.unmodelled IRFault.float_domain)",
            ),
            "The verdict for every float-domain operation: there is no float value domain, so \
             the result is a tagged unmodelled outcome rather than an invented number.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_width_fault : IRStepResult := ",
                "IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded)",
            ),
            "The verdict for remaining representation-dependent operations (Overflow's paired \
             result, representation casts, and provenance-free integer-to-pointer conversion).",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_int2_wrap (f : Nat -> Nat -> Nat -> Nat) (t : IRTy) ",
                "(a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (w : Nat) => ir_int2 (fun (x : Nat) (y : Nat) => ",
                "IRStepResult.value (IRScalar.int_ (f w x y))) a b) ",
                "(ir_ty_int_width t)",
            ),
            "Apply an exact width-indexed binary integer operation. The instruction's IRTy is \
             semantic input, not decoration: non-integer types fail closed and results are \
             canonical residues.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_int1_wrap (f : Nat -> Nat -> Nat) (t : IRTy) ",
                "(a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (w : Nat) => ir_int1 (fun (x : Nat) => ",
                "IRStepResult.value (IRScalar.int_ (f w x))) a) ",
                "(ir_ty_int_width t)",
            ),
            "Unary counterpart of ir_int2_wrap.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_int2_width_result (f : Nat -> Nat -> Nat -> IRStepResult) (t : IRTy) ",
                "(a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (w : Nat) => ir_int2 (fun (x : Nat) (y : Nat) => ",
                "f w (ir_wrap w x) (ir_wrap w y)) a b) (ir_ty_int_width t)",
            ),
            "Apply a width-indexed integer operation whose exact semantics can return either a \
             value or a UB fault.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_sdiv_bits (w : Nat) (x : Nat) (y : Nat) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.value (IRScalar.int_ (ir_signed_encode w ",
                "(ir_bool_xor (ir_sign_bit w x) (ir_sign_bit w y)) ",
                "(ir_nat_div (ir_signed_magnitude w x) (ir_signed_magnitude w y))))) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.div_overflow)) ",
                "(Bool.and ",
                "(ir_nat_eqb x (ir_nat_pow2 (Nat.pred w))) ",
                "(ir_nat_eqb y (Nat.pred (ir_nat_pow2 w))))) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.div_zero)) ",
                "(ir_nat_eqb y Nat.zero)",
            ),
            "Exact signed division with truncation toward zero. Zero divisors and MIN/-1 are the \
             two UB cases in trust-ir's executable interpreter.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_srem_bits (w : Nat) (x : Nat) (y : Nat) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.value (IRScalar.int_ (ir_signed_encode w ",
                "(ir_sign_bit w x) ",
                "(ir_nat_rem (ir_signed_magnitude w x) (ir_signed_magnitude w y))))) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.div_overflow)) ",
                "(Bool.and ",
                "(ir_nat_eqb x (ir_nat_pow2 (Nat.pred w))) ",
                "(ir_nat_eqb y (Nat.pred (ir_nat_pow2 w))))) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.div_zero)) ",
                "(ir_nat_eqb y Nat.zero)",
            ),
            "Exact signed remainder; the result has the dividend's sign and shares SDiv's UB \
             policy, matching trust-ir's executable interpreter.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_shl_bits (w : Nat) (x : Nat) (amount : Nat) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.shift_oob)) ",
                "(IRStepResult.value (IRScalar.int_ ",
                "(ir_wrap w (ir_nat_mul x (ir_nat_pow2 amount))))) ",
                "(ir_nat_ltb amount w)",
            ),
            "Exact wrapping left shift; an amount greater than or equal to the width is UB.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_lshr_bits (w : Nat) (x : Nat) (amount : Nat) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.shift_oob)) ",
                "(IRStepResult.value (IRScalar.int_ ",
                "(ir_nat_div x (ir_nat_pow2 amount)))) ",
                "(ir_nat_ltb amount w)",
            ),
            "Exact logical right shift with trust-ir's out-of-range UB policy.",
        )?;

        self.add_recursive_def(
            r"def ir_ashr_value (w : Nat) (x : Nat) (amount : Nat) : Nat := match ir_sign_bit w x with
| false => ir_nat_div x (ir_nat_pow2 amount)
| true => Nat.add (ir_nat_div x (ir_nat_pow2 amount)) (Nat.sub (ir_nat_pow2 w) (ir_nat_div (ir_nat_pow2 w) (ir_nat_pow2 amount)))",
            "Arithmetic-right-shift bit pattern: logical quotient plus the high-one fill for a \
             negative source.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_ashr_bits (w : Nat) (x : Nat) (amount : Nat) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.shift_oob)) ",
                "(IRStepResult.value (IRScalar.int_ (ir_ashr_value w x amount))) ",
                "(ir_nat_ltb amount w)",
            ),
            "Exact arithmetic right shift with sign fill and trust-ir's out-of-range UB policy.",
        )?;

        self.add_recursive_def(
            r"def ir_bitop_typed (op : Bool -> Bool -> Bool) (t : IRTy) (a : IRScalar) (b : IRScalar) : IRStepResult := match t with
| IRTy.bool_ => ir_bitop op a b
| IRTy.int_ w => ir_int2 (fun (x : Nat) (y : Nat) => IRStepResult.value (IRScalar.int_ (ir_nat_bitop op w x y))) a b
| IRTy.uint_ w => ir_int2 (fun (x : Nat) (y : Nat) => IRStepResult.value (IRScalar.int_ (ir_nat_bitop op w x y))) a b
| IRTy.float_ w => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.ptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.ref_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.refmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rawconst_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rawmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rc_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.fatptr_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.never_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.tuple_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.array_ e n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.struct_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.enum_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.func_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            "Typed And/Or/Xor: exact Bool behavior at i1 and exact width-bounded bit behavior for \
             integer carriers.",
        )?;

        self.add_recursive_def(
            r"def ir_uint2 (f : Nat -> Nat -> IRStepResult) (t : IRTy) (a : IRScalar) (b : IRScalar) : IRStepResult := match t with
| IRTy.bool_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.int_ w => ir_int2 (fun (x : Nat) (y : Nat) => f (ir_wrap w x) (ir_wrap w y)) a b
| IRTy.uint_ w => ir_int2 (fun (x : Nat) (y : Nat) => f (ir_wrap w x) (ir_wrap w y)) a b
| IRTy.float_ w => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.ptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.ref_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.refmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rawconst_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rawmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rc_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.fatptr_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.never_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.tuple_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.array_ e n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.struct_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.enum_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.func_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            "Run an unsigned integer operation on canonical width-w residues. Both signed- and \
             unsigned-declared integer types carry the same width-w bit patterns; the opcode, \
             rather than the carrier type, selects unsigned interpretation.",
        )?;

        self.add_recursive_def(
            r"def ir_binop_eval (op : IRBinOp) (t : IRTy) (a : IRScalar) (b : IRScalar) : IRStepResult := match op with
| IRBinOp.add => ir_int2_wrap (fun (w : Nat) (x : Nat) (y : Nat) => ir_wrap w (Nat.add x y)) t a b
| IRBinOp.sub => ir_int2_wrap ir_sub_wrap t a b
| IRBinOp.mul => ir_int2_wrap (fun (w : Nat) (x : Nat) (y : Nat) => ir_wrap w (ir_nat_mul x y)) t a b
| IRBinOp.udiv => ir_uint2 ir_div_checked t a b
| IRBinOp.sdiv => ir_int2_width_result ir_sdiv_bits t a b
| IRBinOp.urem => ir_uint2 ir_rem_checked t a b
| IRBinOp.srem => ir_int2_width_result ir_srem_bits t a b
| IRBinOp.fadd => ir_float_fault
| IRBinOp.fsub => ir_float_fault
| IRBinOp.fmul => ir_float_fault
| IRBinOp.fdiv => ir_float_fault
| IRBinOp.frem => ir_float_fault
| IRBinOp.fmin => ir_float_fault
| IRBinOp.fmax => ir_float_fault
| IRBinOp.and_ => ir_bitop_typed Bool.and t a b
| IRBinOp.or_ => ir_bitop_typed Bool.or t a b
| IRBinOp.xor_ => ir_bitop_typed ir_bool_xor t a b
| IRBinOp.shl => ir_int2_width_result ir_shl_bits t a b
| IRBinOp.lshr => ir_int2_width_result ir_lshr_bits t a b
| IRBinOp.ashr => ir_int2_width_result ir_ashr_bits t a b",
            "BinOp semantics, 20/20 arms. Typed Add/Sub/Mul use exact modulo-2^w machine \
             arithmetic; signed/unsigned division and remainder, And/Or/Xor, and all three shifts \
             match trust-ir's executable bit-pattern semantics. Division by zero, MIN/-1, and an \
             amount greater than or equal to the width are explicit UB outcomes.",
        )?;

        self.add_recursive_def(
            "def ir_u2 : IRTy := IRTy.uint_ (Nat.succ (Nat.succ Nat.zero))",
            "Two-bit unsigned type used by the executable wrapping-arithmetic ratchet.",
        )?;

        self.add_recursive_def(
            "def ir_i4 : IRTy := IRTy.int_ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))",
            "Four-bit signed type used by the executable two's-complement ratchet.",
        )?;

        self.add_recursive_def(
            "def ir_exact_add_wraps : Eq IRStepResult (ir_binop_eval IRBinOp.add ir_u2 (IRScalar.int_ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (IRScalar.int_ (Nat.succ (Nat.succ Nat.zero)))) (IRStepResult.value (IRScalar.int_ (Nat.succ Nat.zero))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (Nat.succ Nat.zero)))",
            "Kernel-executed width-2 addition witness: 3 + 2 wraps to 1.",
        )?;

        self.add_recursive_def(
            "def ir_exact_sub_wraps : Eq IRStepResult (ir_binop_eval IRBinOp.sub ir_u2 (IRScalar.int_ Nat.zero) (IRScalar.int_ (Nat.succ (Nat.succ Nat.zero)))) (IRStepResult.value (IRScalar.int_ (Nat.succ (Nat.succ Nat.zero)))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (Nat.succ (Nat.succ Nat.zero))))",
            "Kernel-executed width-2 subtraction witness: 0 - 2 wraps to 2.",
        )?;

        self.add_recursive_def(
            "def ir_exact_mul_wraps : Eq IRStepResult (ir_binop_eval IRBinOp.mul ir_u2 (IRScalar.int_ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (IRScalar.int_ (Nat.succ (Nat.succ Nat.zero)))) (IRStepResult.value (IRScalar.int_ (Nat.succ (Nat.succ Nat.zero)))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (Nat.succ (Nat.succ Nat.zero))))",
            "Kernel-executed width-2 multiplication witness: 3 * 2 wraps to 2.",
        )?;

        self.add_recursive_def(
            "def ir_exact_sdiv_negative : Eq IRStepResult (ir_binop_eval IRBinOp.sdiv ir_i4 (IRScalar.int_ 13) (IRScalar.int_ 2)) (IRStepResult.value (IRScalar.int_ 15)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 15))",
            "Differential vector from trust-ir::eval_int_binop: i4(-3) / i4(2) truncates toward \
             zero to the bit pattern 15 (-1).",
        )?;

        self.add_recursive_def(
            "def ir_exact_srem_negative : Eq IRStepResult (ir_binop_eval IRBinOp.srem ir_i4 (IRScalar.int_ 13) (IRScalar.int_ 2)) (IRStepResult.value (IRScalar.int_ 15)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 15))",
            "Differential vector: signed remainder retains the dividend sign.",
        )?;

        self.add_recursive_def(
            "def ir_sdiv_min_overflow : Eq IRStepResult (ir_binop_eval IRBinOp.sdiv ir_i4 (IRScalar.int_ 8) (IRScalar.int_ 15)) (IRStepResult.fault (IROutcome.ub IRFault.div_overflow)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.div_overflow))",
            "Differential UB vector: i4::MIN / -1 is signed division overflow.",
        )?;

        self.add_recursive_def(
            "def ir_sdiv_zero_ub : Eq IRStepResult (ir_binop_eval IRBinOp.sdiv ir_i4 (IRScalar.int_ 8) (IRScalar.int_ 0)) (IRStepResult.fault (IROutcome.ub IRFault.div_zero)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.div_zero))",
            "Differential UB vector: signed division by zero is never a value.",
        )?;

        self.add_recursive_def(
            "def ir_exact_shl : Eq IRStepResult (ir_binop_eval IRBinOp.shl ir_i4 (IRScalar.int_ 3) (IRScalar.int_ 2)) (IRStepResult.value (IRScalar.int_ 12)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 12))",
            "Differential vector: width-four 3 << 2 is 12.",
        )?;

        self.add_recursive_def(
            "def ir_exact_lshr : Eq IRStepResult (ir_binop_eval IRBinOp.lshr ir_i4 (IRScalar.int_ 12) (IRScalar.int_ 2)) (IRStepResult.value (IRScalar.int_ 3)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 3))",
            "Differential vector: logical right shift fills with zeroes.",
        )?;

        self.add_recursive_def(
            "def ir_exact_ashr : Eq IRStepResult (ir_binop_eval IRBinOp.ashr ir_i4 (IRScalar.int_ 12) (IRScalar.int_ 1)) (IRStepResult.value (IRScalar.int_ 14)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 14))",
            "Differential vector: i4(-4) >> 1 sign-fills to i4(-2), bit pattern 14.",
        )?;

        self.add_recursive_def(
            "def ir_shift_oversize_ub : Eq IRStepResult (ir_binop_eval IRBinOp.shl ir_i4 (IRScalar.int_ 1) (IRScalar.int_ 4)) (IRStepResult.fault (IROutcome.ub IRFault.shift_oob)) := Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.shift_oob))",
            "Differential UB vector: a shift amount equal to the integer width is out of range.",
        )?;

        self.add_recursive_def(
            "def ir_exact_integer_and : Eq IRStepResult (ir_binop_eval IRBinOp.and_ ir_i4 (IRScalar.int_ 10) (IRScalar.int_ 12)) (IRStepResult.value (IRScalar.int_ 8)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 8))",
            "Differential vector: 0b1010 AND 0b1100 is 0b1000.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_not_eval (t : IRTy) (a : IRScalar) : IRStepResult := match t with ",
                "| IRTy.bool_ => IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (x : Bool) => IRStepResult.value (IRScalar.bool_ (Bool.not x))) (ir_as_bool a) ",
                "| IRTy.int_ w => ir_int1 (fun (x : Nat) => IRStepResult.value (IRScalar.int_ (ir_nat_bitnot w x))) a ",
                "| IRTy.uint_ w => ir_int1 (fun (x : Nat) => IRStepResult.value (IRScalar.int_ (ir_nat_bitnot w x))) a ",
                "| _ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            ),
            "Typed logical/bitwise complement: Bool.not for i1 and exact mask complement for \
             integer carriers.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_ctpop_eval (t : IRTy) (a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (w : Nat) => ir_int1 (fun (x : Nat) => IRStepResult.value ",
                "(IRScalar.int_ (ir_wrap w (ir_nat_ctpop w x)))) a) (ir_ty_int_width t)",
            ),
            "Exact population count, returned in the instruction's integer carrier.",
        )?;

        self.add_recursive_def(
            r"def ir_unop_eval (op : IRUnOp) (t : IRTy) (a : IRScalar) : IRStepResult := match op with
| IRUnOp.neg => ir_int1_wrap (fun (w : Nat) (x : Nat) => ir_sub_wrap w Nat.zero x) t a
| IRUnOp.fneg => ir_float_fault
| IRUnOp.fabs => ir_float_fault
| IRUnOp.fsqrt => ir_float_fault
| IRUnOp.ffloor => ir_float_fault
| IRUnOp.fceil => ir_float_fault
| IRUnOp.ftrunc => ir_float_fault
| IRUnOp.not_ => ir_not_eval t a
| IRUnOp.ctpop => ir_ctpop_eval t a",
            "UnOp semantics, 9/9 arms.",
        )?;

        self.add_recursive_def(
            "def ir_exact_integer_not : Eq IRStepResult (ir_unop_eval IRUnOp.not_ ir_i4 (IRScalar.int_ 10)) (IRStepResult.value (IRScalar.int_ 5)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 5))",
            "Differential vector: NOT 0b1010 at width four is 0b0101.",
        )?;

        self.add_recursive_def(
            "def ir_exact_integer_ctpop : Eq IRStepResult (ir_unop_eval IRUnOp.ctpop ir_i4 (IRScalar.int_ 11)) (IRStepResult.value (IRScalar.int_ 3)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 3))",
            "Differential vector: ctpop(0b1011) is three.",
        )?;

        Ok(())
    }

    /// ICmp (10/10) and FCmp (12/12).
    fn add_eval_ir_compare(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_int_cmp (f : Nat -> Nat -> Bool) (t : IRTy) ",
                "(a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (w : Nat) => ir_int2 (fun (x : Nat) (y : Nat) => ",
                "IRStepResult.value (IRScalar.bool_ (f (ir_wrap w x) (ir_wrap w y)))) a b) ",
                "(ir_ty_int_width t)",
            ),
            "Compare integer bit patterns after canonicalizing both operands at the declared \
             width. This prevents out-of-range Nat carriers from changing machine comparisons.",
        )?;

        self.add_recursive_def(
            r"def ir_icmp_eq (t : IRTy) (a : IRScalar) (b : IRScalar) : IRStepResult := match t with
| IRTy.int_ w => ir_int_cmp ir_nat_eqb t a b
| IRTy.uint_ w => ir_int_cmp ir_nat_eqb t a b
| IRTy.bool_ => ir_bool_result (ir_eqb a b)
| IRTy.float_ w => ir_bool_result (ir_eqb a b)
| IRTy.ptr_ => ir_bool_result (ir_eqb a b)
| IRTy.ref_ p => ir_bool_result (ir_eqb a b)
| IRTy.refmut_ p => ir_bool_result (ir_eqb a b)
| IRTy.rawconst_ p => ir_bool_result (ir_eqb a b)
| IRTy.rawmut_ p => ir_bool_result (ir_eqb a b)
| IRTy.rc_ p => ir_bool_result (ir_eqb a b)
| IRTy.fatptr_ p => ir_bool_result (ir_eqb a b)
| IRTy.unit_ => ir_bool_result (ir_eqb a b)
| IRTy.never_ => ir_bool_result (ir_eqb a b)
| IRTy.tuple_ n => ir_bool_result (ir_eqb a b)
| IRTy.array_ e n => ir_bool_result (ir_eqb a b)
| IRTy.struct_ n => ir_bool_result (ir_eqb a b)
| IRTy.enum_ n => ir_bool_result (ir_eqb a b)
| IRTy.func_ n => ir_bool_result (ir_eqb a b)",
            "Typed equality. Integer operands compare canonical width-w bit patterns; the \
             existing exact comparable-value relation handles bools, unit, and pointer-shaped \
             values used by the crystal.",
        )?;

        self.add_recursive_def(
            r"def ir_icmp_ne (t : IRTy) (a : IRScalar) (b : IRScalar) : IRStepResult := match t with
| IRTy.int_ w => ir_int_cmp (fun (x : Nat) (y : Nat) => Bool.not (ir_nat_eqb x y)) t a b
| IRTy.uint_ w => ir_int_cmp (fun (x : Nat) (y : Nat) => Bool.not (ir_nat_eqb x y)) t a b
| IRTy.bool_ => ir_bool_result_neg (ir_eqb a b)
| IRTy.float_ w => ir_bool_result_neg (ir_eqb a b)
| IRTy.ptr_ => ir_bool_result_neg (ir_eqb a b)
| IRTy.ref_ p => ir_bool_result_neg (ir_eqb a b)
| IRTy.refmut_ p => ir_bool_result_neg (ir_eqb a b)
| IRTy.rawconst_ p => ir_bool_result_neg (ir_eqb a b)
| IRTy.rawmut_ p => ir_bool_result_neg (ir_eqb a b)
| IRTy.rc_ p => ir_bool_result_neg (ir_eqb a b)
| IRTy.fatptr_ p => ir_bool_result_neg (ir_eqb a b)
| IRTy.unit_ => ir_bool_result_neg (ir_eqb a b)
| IRTy.never_ => ir_bool_result_neg (ir_eqb a b)
| IRTy.tuple_ n => ir_bool_result_neg (ir_eqb a b)
| IRTy.array_ e n => ir_bool_result_neg (ir_eqb a b)
| IRTy.struct_ n => ir_bool_result_neg (ir_eqb a b)
| IRTy.enum_ n => ir_bool_result_neg (ir_eqb a b)
| IRTy.func_ n => ir_bool_result_neg (ir_eqb a b)",
            "Typed inequality, with the same integer canonicalization as ir_icmp_eq.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_signed_cmp (relation : Nat -> Nat -> Nat -> Bool) ",
                "(t : IRTy) (a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (w : Nat) => ir_int2 (fun (x : Nat) (y : Nat) => ",
                "IRStepResult.value (IRScalar.bool_ (relation w x y))) a b) ",
                "(ir_ty_int_width t)",
            ),
            "Apply an exact width-indexed signed comparison to integer operands.",
        )?;

        self.add_recursive_def(
            r"def ir_icmp_eval (op : IRICmpOp) (t : IRTy) (a : IRScalar) (b : IRScalar) : IRStepResult := match op with
| IRICmpOp.eq_ => ir_icmp_eq t a b
| IRICmpOp.ne_ => ir_icmp_ne t a b
| IRICmpOp.ult => ir_int_cmp ir_nat_ltb t a b
| IRICmpOp.ule => ir_int_cmp ir_nat_leb t a b
| IRICmpOp.ugt => ir_int_cmp (fun (x : Nat) (y : Nat) => ir_nat_ltb y x) t a b
| IRICmpOp.uge => ir_int_cmp (fun (x : Nat) (y : Nat) => ir_nat_leb y x) t a b
| IRICmpOp.slt => ir_signed_cmp ir_signed_ltb t a b
| IRICmpOp.sle => ir_signed_cmp (fun (w : Nat) (x : Nat) (y : Nat) => Bool.or (ir_signed_ltb w x y) (ir_nat_eqb (ir_wrap w x) (ir_wrap w y))) t a b
| IRICmpOp.sgt => ir_signed_cmp (fun (w : Nat) (x : Nat) (y : Nat) => ir_signed_ltb w y x) t a b
| IRICmpOp.sge => ir_signed_cmp (fun (w : Nat) (x : Nat) (y : Nat) => Bool.or (ir_signed_ltb w y x) (ir_nat_eqb (ir_wrap w x) (ir_wrap w y))) t a b",
            "ICmp semantics, 10/10 arms. Equality and unsigned ordering are exact over canonical \
             width-w bit patterns, and signed ordering interprets the same patterns as exact \
             two's-complement values. Equality for bools, unit, and pointer-shaped values remains \
             exact; unsupported comparable domains retain their existing tagged decline.",
        )?;

        self.add_recursive_def(
            "def ir_exact_slt_sign_boundary : Eq IRStepResult (ir_icmp_eval IRICmpOp.slt ir_i4 (IRScalar.int_ 8) (IRScalar.int_ 7)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))",
            "Differential vector: i4::MIN is signed-less-than i4::MAX across the sign boundary.",
        )?;

        self.add_recursive_def(
            "def ir_exact_sgt_negative_pair : Eq IRStepResult (ir_icmp_eval IRICmpOp.sgt ir_i4 (IRScalar.int_ 15) (IRScalar.int_ 8)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))",
            "Differential vector: i4(-1) is signed-greater-than i4(-8).",
        )?;

        self.add_recursive_def(
            r"def ir_fcmp_eval (op : IRFCmpOp) (a : IRScalar) (b : IRScalar) : IRStepResult := match op with
| IRFCmpOp.oeq => ir_float_fault
| IRFCmpOp.one_ => ir_float_fault
| IRFCmpOp.olt => ir_float_fault
| IRFCmpOp.ole => ir_float_fault
| IRFCmpOp.ogt => ir_float_fault
| IRFCmpOp.oge => ir_float_fault
| IRFCmpOp.ueq => ir_float_fault
| IRFCmpOp.une => ir_float_fault
| IRFCmpOp.ult => ir_float_fault
| IRFCmpOp.ule => ir_float_fault
| IRFCmpOp.ugt => ir_float_fault
| IRFCmpOp.uge => ir_float_fault",
            "FCmp semantics, 12/12 arms — every one the tagged `unmodelled float_domain` \
             outcome. The arms are enumerated rather than collapsed so the coverage claim is \
             checkable constructor-by-constructor and so a future float domain has 12 named \
             places to land.",
        )?;

        Ok(())
    }

    /// Cast (17/17).
    fn add_eval_ir_cast(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_trunc_int (sw : Nat) (dst : IRTy) (a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (dw : Nat) => Bool.rec (fun (_ : Bool) => IRStepResult) ir_width_fault ",
                "(ir_int1 (fun (x : Nat) => IRStepResult.value (IRScalar.int_ (ir_wrap dw x))) a) ",
                "(ir_nat_leb dw sw)) (ir_ty_int_width dst)",
            ),
            "Exact integer truncation to an integer destination. The destination width must not \
             exceed the source width; the result is the canonical low-width residue.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_trunc_bool (sw : Nat) (a : IRScalar) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ir_width_fault ",
                "(ir_int1 (fun (x : Nat) => Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.value (IRScalar.bool_ Bool.true)) ",
                "(IRStepResult.value (IRScalar.bool_ Bool.false)) ",
                "(ir_nat_eqb (ir_wrap (Nat.succ Nat.zero) x) Nat.zero)) a) ",
                "(ir_nat_leb (Nat.succ Nat.zero) sw)",
            ),
            "Exact truncation to i1/Bool: require a source at least one bit wide, retain the low \
             bit, and materialize the Bool carrier.",
        )?;

        self.add_recursive_def(
            r"def ir_trunc_eval (src : IRTy) (dst : IRTy) (a : IRScalar) : IRStepResult := match src with
| IRTy.int_ sw => match dst with
  | IRTy.bool_ => ir_trunc_bool sw a
  | IRTy.int_ dw => ir_trunc_int sw dst a
  | IRTy.uint_ dw => ir_trunc_int sw dst a
  | IRTy.float_ w => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.ptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.ref_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.refmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.rawconst_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.rawmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.rc_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.fatptr_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.never_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.tuple_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.array_ e n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.struct_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.enum_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.func_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.uint_ sw => match dst with
  | IRTy.bool_ => ir_trunc_bool sw a
  | IRTy.int_ dw => ir_trunc_int sw dst a
  | IRTy.uint_ dw => ir_trunc_int sw dst a
  | IRTy.float_ w => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.ptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.ref_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.refmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.rawconst_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.rawmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.rc_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.fatptr_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.never_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.tuple_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.array_ e n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.struct_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.enum_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
  | IRTy.func_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.bool_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.float_ w => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.ptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.ref_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.refmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rawconst_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rawmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rc_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.fatptr_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.never_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.tuple_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.array_ e n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.struct_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.enum_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.func_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            "Typed truncation from a machine integer to a narrower machine integer or Bool.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_zext_int (sw : Nat) (dst : IRTy) (a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (dw : Nat) => Bool.rec (fun (_ : Bool) => IRStepResult) ir_width_fault ",
                "(ir_int1 (fun (x : Nat) => IRStepResult.value ",
                "(IRScalar.int_ (ir_wrap dw (ir_wrap sw x)))) a) (ir_nat_leb sw dw)) ",
                "(ir_ty_int_width dst)",
            ),
            "Exact zero extension: canonicalize at the source width, then embed in the no-smaller \
             destination width.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_zext_bool (dst : IRTy) (a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (dw : Nat) => Bool.rec (fun (_ : Bool) => IRStepResult) ir_width_fault ",
                "(IROption.rec Bool ",
                "(fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (b : Bool) => IRStepResult.value (IRScalar.int_ ",
                "(Bool.rec (fun (_ : Bool) => Nat) Nat.zero (Nat.succ Nat.zero) b))) ",
                "(ir_as_bool a)) (ir_nat_leb (Nat.succ Nat.zero) dw)) (ir_ty_int_width dst)",
            ),
            "Exact zero extension from Bool/i1 to a non-zero-width integer carrier.",
        )?;

        self.add_recursive_def(
            r"def ir_zext_eval (src : IRTy) (dst : IRTy) (a : IRScalar) : IRStepResult := match src with
| IRTy.bool_ => ir_zext_bool dst a
| IRTy.int_ sw => ir_zext_int sw dst a
| IRTy.uint_ sw => ir_zext_int sw dst a
| IRTy.float_ w => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.ptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.ref_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.refmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rawconst_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rawmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.rc_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.fatptr_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.never_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.tuple_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.array_ e n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.struct_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.enum_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRTy.func_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            "Typed zero extension. It remains distinct from the exact sign-extension operation \
             below, so the two cast opcodes cannot be conflated.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_sext_value (sw : Nat) (dw : Nat) (value : Nat) : Nat := ",
                "Bool.rec (fun (_ : Bool) => Nat) (ir_wrap sw value) ",
                "(Nat.add (ir_wrap sw value) ",
                "(Nat.sub (ir_nat_pow2 dw) (ir_nat_pow2 sw))) ",
                "(ir_sign_bit sw value)",
            ),
            "Exact sign-extension bit pattern before destination canonicalization.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_sext_int (sw : Nat) (dst : IRTy) (a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (dw : Nat) => Bool.rec (fun (_ : Bool) => IRStepResult) ir_width_fault ",
                "(ir_int1 (fun (x : Nat) => IRStepResult.value ",
                "(IRScalar.int_ (ir_wrap dw (ir_sext_value sw dw x)))) a) ",
                "(ir_nat_leb sw dw)) (ir_ty_int_width dst)",
            ),
            "Exact sign extension from a non-wider integer source.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_sext_bool (dst : IRTy) (a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (dw : Nat) => Bool.rec (fun (_ : Bool) => IRStepResult) ir_width_fault ",
                "(IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (bit : Bool) => IRStepResult.value (IRScalar.int_ ",
                "(Bool.rec (fun (_ : Bool) => Nat) Nat.zero ",
                "(Nat.pred (ir_nat_pow2 dw)) bit))) (ir_as_bool a)) ",
                "(ir_nat_leb (Nat.succ Nat.zero) dw)) (ir_ty_int_width dst)",
            ),
            "Exact sign extension from i1/Bool: true is the all-ones destination pattern.",
        )?;

        self.add_recursive_def(
            r"def ir_sext_eval (src : IRTy) (dst : IRTy) (a : IRScalar) : IRStepResult := match src with
| IRTy.bool_ => ir_sext_bool dst a
| IRTy.int_ sw => ir_sext_int sw dst a
| IRTy.uint_ sw => ir_sext_int sw dst a
| _ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            "Typed exact two's-complement sign extension.",
        )?;

        self.add_recursive_def(
            r"def ir_ptrtoint_width (w : Nat) (a : IRScalar) : IRStepResult := match a with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => IRStepResult.value (IRScalar.int_ (ir_wrap w a))
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded)
| IRScalar.fat_ d md => IRStepResult.value (IRScalar.int_ (ir_wrap w d))
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "PtrToInt at an established destination width. `nullptr_` is NOT mapped to integer \
             zero: this model's addresses do \
             not reserve zero for null (nullptr_ is its own constructor), so there is no correct \
             integer to give — the honest answer is the tagged unmodelled outcome.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_ptrtoint_eval (dst : IRTy) (a : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (w : Nat) => ir_ptrtoint_width w a) (ir_ty_int_width dst)",
            ),
            "Typed PtrToInt wrapper: the instruction's destination width is semantic input.",
        )?;

        self.add_recursive_def(
            r"def ir_ptrcast_eval (a : IRScalar) : IRStepResult := match a with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => IRStepResult.value (IRScalar.ptr_ a)
| IRScalar.nullptr_ => IRStepResult.value IRScalar.nullptr_
| IRScalar.fat_ d md => IRStepResult.value (IRScalar.fat_ d md)
| IRScalar.fnptr_ f => IRStepResult.value (IRScalar.fnptr_ f)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "PtrToPtr: provenance-preserving identity on the pointer-like values. This is the \
             cast a `&Level -> &Level` coercion lowers to, so it is on the crystal's path.",
        )?;

        self.add_recursive_def(
            r"def ir_reifyfn_eval (a : IRScalar) : IRStepResult := match a with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.ptr_ a => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.fat_ d md => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.fnptr_ f => IRStepResult.value (IRScalar.fnptr_ f)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_fnptr)",
            "ReifyFnPointer: identity on a function pointer.",
        )?;

        self.add_recursive_def(
            r"def ir_cast_eval (op : IRCastOp) (src : IRTy) (dst : IRTy) (a : IRScalar) : IRStepResult := match op with
| IRCastOp.trunc => ir_trunc_eval src dst a
| IRCastOp.zext => ir_zext_eval src dst a
| IRCastOp.sext => ir_sext_eval src dst a
| IRCastOp.fptrunc => ir_float_fault
| IRCastOp.fpext => ir_float_fault
| IRCastOp.fptoui => ir_float_fault
| IRCastOp.fptosi => ir_float_fault
| IRCastOp.uitofp => ir_float_fault
| IRCastOp.sitofp => ir_float_fault
| IRCastOp.ptrtoint => ir_ptrtoint_eval dst a
| IRCastOp.inttoptr => ir_width_fault
| IRCastOp.ptrtoptr => ir_ptrcast_eval a
| IRCastOp.bitcast => ir_width_fault
| IRCastOp.transmute => ir_width_fault
| IRCastOp.reifyfnpointer => ir_reifyfn_eval a
| IRCastOp.fptosisat => ir_float_fault
| IRCastOp.fptouisat => ir_float_fault",
            "Cast semantics, 17/17 arms. bitcast and transmute are REPRESENTATION-level \
             reinterpretations; a cell-addressed model has no representation to reinterpret, so \
             they are the tagged `unmodelled width_bounded` outcome rather than a silent \
             identity that would be wrong for e.g. transmute::<f64, u64>.",
        )?;

        self.add_recursive_def(
            "def ir_u4 : IRTy := IRTy.uint_ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))",
            "Four-bit unsigned type used by the executable cast ratchet.",
        )?;

        self.add_recursive_def(
            "def ir_exact_trunc_low_bit : Eq IRStepResult (ir_cast_eval IRCastOp.trunc ir_u2 IRTy.bool_ (IRScalar.int_ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))",
            "Kernel-executed cast witness: truncating two-bit 3 to i1 keeps the low bit.",
        )?;

        self.add_recursive_def(
            "def ir_exact_zext_canonicalizes : Eq IRStepResult (ir_cast_eval IRCastOp.zext ir_u2 ir_u4 (IRScalar.int_ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))) (IRStepResult.value (IRScalar.int_ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
            "Kernel-executed cast witness: zero-extension first canonicalizes 7 at source width \
             two, producing 3 at destination width four.",
        )?;

        self.add_recursive_def(
            "def ir_exact_sext_negative : Eq IRStepResult (ir_cast_eval IRCastOp.sext ir_u2 ir_u4 (IRScalar.int_ 3)) (IRStepResult.value (IRScalar.int_ 15)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ 15))",
            "Differential vector: sign-extending two-bit -1 (pattern 3) to four bits yields the \
             all-ones pattern 15.",
        )?;

        self.add_recursive_def(
            "def ir_inttoptr_fails_closed : Eq IRStepResult (ir_cast_eval IRCastOp.inttoptr ir_u4 IRTy.ptr_ (IRScalar.int_ Nat.zero)) ir_width_fault := Eq.refl IRStepResult ir_width_fault",
            "Kernel-executed negative witness: integer zero does not manufacture a dereferenceable \
             pointer in the abstract provenance model.",
        )?;

        Ok(())
    }
}
