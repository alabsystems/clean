// Copyright 2026 Andrew Yates.
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
//! EvalIR — Clean-side executable semantics for the emitted trust-ir fragment
//! (plan job C3, `designs/2026-07-29-evalir-value-domain.md`).
//!
//! Mirrors (by hand, READ-ONLY — nothing generated, no Lean enters clean) the
//! Lean reference semantics at `~/trust-ir/lean/trust_ir-semantics/`:
//! - value domain: `TrustIr/State/ValueMap.lean:25-80` (`Value`), restricted
//!   to the fragment, with LOGICAL tagged enum/aggregate values (the Lean
//!   `semLoad` rejects `Ty::Enum` — no byte size, `Semantics/Memory.lean:
//!   89-116,246` — which is exactly why this Clean-side semantics exists;
//!   layout adequacy is a separate per-type obligation, design §2.1);
//! - machine state: `TrustIr/State/MachineState.lean:27-60` (`locals` +
//!   `nextValueId` modeled as one positional list, append = `bindValue`);
//! - arithmetic: `TrustIr/Semantics/Arith.lean:61-67,313-341` (`semIntBinOp`
//!   wrapping semantics, `semBinOp` operand-width agreement);
//! - dispatch/fuel: `TrustIr/Semantics/Step.lean:68-...` (`stepInst`) and
//!   `TrustIr/Semantics/Eval.lean:135-152` (`stepN`, fuel-based), in the
//!   validated `whnf_fuel_red` executable-relation idiom
//!   (`core_spec/whnf_progress.rs:562`): fuel-indexed, OptionType-valued,
//!   `none` = honest bail / fail-closed stuckness, `some` = real verdict.
//!
//! Wave-1 slice: straight-line integer arithmetic — `Const` / `BinOp`
//! (`add`/`sub`/`mul`) / `Return` — 3 of the 28 producer-constructed `Inst`
//! variants (G2 census re-derived with citations in the design §3.1). Every
//! rule carries a concrete `Eq.refl` execution witness the kernel must RUN to
//! accept, plus fail-closed and fuel-bail witnesses.
//!
//! ZERO new axioms: every declaration is a valued inductive/def; census stays
//! at 11.
//!
//! NOT WIRED into the live bundle this wave (bundles.rs is another lane's).
//! The `#[cfg(test)]` suite below builds these decls on the Substitution test
//! bundle — the same foundation + expr_model + rec_env substrate the live
//! wiring will use — so everything here is already elaborated and
//! kernel-checked by `cargo test --locked -p clean-verify --lib evalir`.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Register the EvalIR value domain, arithmetic substrate, straight-line
    /// evaluator, and non-vacuity witnesses.
    ///
    /// Stage discipline: reads only `Nat`/`Bool`/`Eq`/`ProdType`
    /// (foundation_types), `ListType` (expr_model), `OptionType`/`nat_eqb`
    /// (rec_env) — all strictly earlier stages. Intended wiring: appended as
    /// the LAST entry of `bundles.rs::STAGES` (diff in the design doc §7).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_evalir(&mut self) -> Result<(), SpecError> {
        self.add_evalir_value_domain()?;
        self.add_evalir_arith_substrate()?;
        self.add_evalir_straightline()?;
        self.add_evalir_witnesses()
    }

    /// The value/heap/instruction inductives (design §2, §3.2).
    fn add_evalir_value_domain(&mut self) -> Result<(), SpecError> {
        // The runtime value domain. Mirrors TrustIr.Value (ValueMap.lean:25-80)
        // restricted to the fragment. Deliberate departures (design §5):
        // ints are width-tagged unsigned residues (no Int in the substrate;
        // equivalent on the wrapped domain); enum/aggregate payloads are a
        // vnil/vcons SPINE internal to the family — a `ListType IRValue`
        // field would be a NESTED inductive occurrence, which kernel
        // add_inductive does not accept (the rose rung models that shape at
        // the object level instead, rose_schema.rs:5-9). Ill-formed spines
        // are representable; representation relations (crystal A2) only
        // construct well-formed ones.
        self.add_inductive(
            r"inductive IRValue : Type
| intv : Nat -> Nat -> IRValue
| boolv : Bool -> IRValue
| unitv : IRValue
| ptrv : Nat -> IRValue
| vnil : IRValue
| vcons : IRValue -> IRValue -> IRValue
| aggv : IRValue -> IRValue
| enumv : Nat -> IRValue -> IRValue",
            "EvalIR runtime value: intv (width, unsigned residue in [0,2^width)), \
             boolv, unitv, ptrv (abstract address), and LOGICAL aggregate/enum \
             values over a vnil/vcons payload spine (tag + payload for enumv). \
             Hand-mirror of TrustIr.Value (ValueMap.lean:25-80) restricted to \
             the emitted fragment; enums are logical because the Lean semLoad \
             rejects Ty::Enum (Memory.lean:89-116,246) — layout adequacy is a \
             separate obligation (C3 design section 2.1).",
        )?;

        // Integer BinOp slice: the three wrapping ops of wave 1.
        self.add_inductive(
            r"inductive IRBinOp : Type
| add : IRBinOp
| sub : IRBinOp
| mul : IRBinOp",
            "EvalIR wave-1 integer binary ops (trust-ir BinOp Add/Sub/Mul, \
             inst.rs:11-14; wrapping semantics per semIntBinOp, \
             Arith.lean:61-67). UDiv/SDiv/URem/SRem/shifts/bitwise/float ops \
             are excluded this wave and named in the C3 design section 3.2.",
        )?;

        // Straight-line instruction slice. Field shapes mirror trust-ir
        // Inst (inst.rs:457): Const{ty,value} -> iconst (width, residue);
        // BinOp{op,ty,lhs,rhs} -> ibinop (op, ty-width, lhs id, rhs id);
        // Return{values} -> iret (single id, the 1-ary slice).
        self.add_inductive(
            r"inductive IRInst : Type
| iconst : Nat -> Nat -> IRInst
| ibinop : IRBinOp -> Nat -> Nat -> Nat -> IRInst
| iret : Nat -> IRInst",
            "EvalIR wave-1 instruction slice: iconst w v (Inst::Const at int \
             type, trust-thir-lower lib.rs:3150), ibinop op w l r (Inst::BinOp, \
             lib.rs:10408), iret v (Inst::Return 1-ary, lib.rs:5445). \
             3 of 28 producer-constructed Inst variants (G2 census, C3 design \
             section 3.1); operand/result ids are dense positional ValueIds.",
        )?;

        // Step outcome: non-terminator -> updated register file; Return ->
        // final value. Mirrors InstrResult (Step.lean:44-47) with the state
        // made explicit (the Sem monad's state is our register list).
        self.add_inductive(
            r"inductive IRStepRes : Type
| next : ListType IRValue -> IRStepRes
| done : IRValue -> IRStepRes",
            "EvalIR single-step outcome: next regs2 (non-terminator bound a \
             value / advanced state) or done v (Return fired). Mirror of \
             InstrResult (Step.lean:44-47) with explicit state.",
        )?;

        // Logical heap lookup: address -> first matching cell's value.
        // ListType/ProdType applied to the ALREADY-registered IRValue —
        // allowed (mirrors ListType Level inside KExpr); nothing in the
        // wave-1 evaluator touches the heap yet (design section 2.3).
        self.add_recursive_def(
            r"def ir_heap_get (h : ListType (ProdType Nat IRValue)) (a : Nat) : OptionType IRValue := ListType.rec (ProdType Nat IRValue) (fun (_h : ListType (ProdType Nat IRValue)) => OptionType IRValue) (OptionType.none IRValue) (fun (cell : ProdType Nat IRValue) (rest : ListType (ProdType Nat IRValue)) (ih : OptionType IRValue) => Bool.rec (fun (_b : Bool) => OptionType IRValue) ih (OptionType.some IRValue (ProdType.snd Nat IRValue cell)) (nat_eqb (ProdType.fst Nat IRValue cell) a)) h",
            "EvalIR logical heap lookup: association-list (addr, value) cells, \
             first match wins. The LOGICAL-cell mirror of the byte Memory \
             (State/Memory.lean) per C3 design section 2.1/2.3; unused by the \
             wave-1 straight-line slice, registered as the heap shape for the \
             crystal's A2 representation relations.",
        )?;

        Ok(())
    }

    /// `Nat` multiplication / power-of-two / modulus — the spec substrate has
    /// no `Nat.mul`/`Nat.mod` primitives (noted at `schema.rs:189`), and the
    /// wrapping semantics (`semIntBinOp`'s `wrap`, Arith.lean:61-67) needs
    /// `mod 2^w`.
    fn add_evalir_arith_substrate(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def ir_nat_mul (a : Nat) (b : Nat) : Nat := match a with
| Nat.zero => Nat.zero
| Nat.succ p => Nat.add b (ir_nat_mul p b)",
            "Nat multiplication by iterated addition (no Nat.mul primitive in \
             the spec substrate, schema.rs:189). EvalIR arithmetic substrate.",
        )?;

        self.add_recursive_def(
            r"def ir_nat_pow2 (w : Nat) : Nat := match w with
| Nat.zero => Nat.succ Nat.zero
| Nat.succ p => Nat.add (ir_nat_pow2 p) (ir_nat_pow2 p)",
            "2^w by doubling. The modulus of width-w wrapping integer \
             arithmetic (semIntBinOp's `modulus`, Arith.lean:62). EvalIR \
             arithmetic substrate.",
        )?;

        // Structural Euclidean remainder: mod 0 b = 0;
        // mod (succ p) b = if (mod p b)+1 == b then 0 else (mod p b)+1.
        // Total (mod a 0 = a); agrees with Euclidean mod for b > 0, which is
        // the only use (b = 2^w > 0). Bool.rec minor order: false-arm first
        // (kernel Bool; same shape as complete_development.rs:103).
        self.add_recursive_def(
            r"def ir_nat_mod (a : Nat) (b : Nat) : Nat := match a with
| Nat.zero => Nat.zero
| Nat.succ p => Bool.rec (fun (_b : Bool) => Nat) (Nat.succ (ir_nat_mod p b)) Nat.zero (nat_eqb (Nat.succ (ir_nat_mod p b)) b)",
            "Structural Nat remainder (counting definition): the successor of \
             the running remainder resets to zero exactly when it reaches the \
             modulus. Total; Euclidean for b > 0 (the only use is b = 2^w). \
             EvalIR arithmetic substrate for wrapping semantics.",
        )?;

        self.add_recursive_def(
            r"def ir_wrap (w : Nat) (n : Nat) : Nat := ir_nat_mod n (ir_nat_pow2 w)",
            "Reduce n to the width-w unsigned residue: n mod 2^w. The Clean \
             mirror of semIntBinOp's `wrap` (Arith.lean:63) on unsigned \
             residues (C3 design section 2.2a).",
        )?;

        Ok(())
    }

    /// The straight-line evaluator: value classifiers, register file
    /// operations, per-instruction step, fuel loop.
    fn add_evalir_straightline(&mut self) -> Result<(), SpecError> {
        // ---- value classifiers / projectors (int case) ----
        self.add_recursive_def(
            r"def ir_val_is_int (v : IRValue) : Bool := match v with
| IRValue.intv w n => Bool.true
| IRValue.boolv b => Bool.false
| IRValue.unitv => Bool.false
| IRValue.ptrv a => Bool.false
| IRValue.vnil => Bool.false
| IRValue.vcons h t => Bool.false
| IRValue.aggv s => Bool.false
| IRValue.enumv tag s => Bool.false",
            "Is this value an integer? True exactly on intv. EvalIR operand \
             classifier (the `.int` pattern of semBinOp, Arith.lean:332).",
        )?;

        self.add_recursive_def(
            r"def ir_val_width (v : IRValue) : Nat := match v with
| IRValue.intv w n => w
| IRValue.boolv b => Nat.zero
| IRValue.unitv => Nat.zero
| IRValue.ptrv a => Nat.zero
| IRValue.vnil => Nat.zero
| IRValue.vcons h t => Nat.zero
| IRValue.aggv s => Nat.zero
| IRValue.enumv tag s => Nat.zero",
            "Width projector: intv's width, zero elsewhere (guarded by \
             ir_val_is_int at every use). EvalIR operand projector.",
        )?;

        self.add_recursive_def(
            r"def ir_val_num (v : IRValue) : Nat := match v with
| IRValue.intv w n => n
| IRValue.boolv b => Nat.zero
| IRValue.unitv => Nat.zero
| IRValue.ptrv a => Nat.zero
| IRValue.vnil => Nat.zero
| IRValue.vcons h t => Nat.zero
| IRValue.aggv s => Nat.zero
| IRValue.enumv tag s => Nat.zero",
            "Residue projector: intv's numeric residue, zero elsewhere \
             (guarded by ir_val_is_int at every use). EvalIR operand \
             projector.",
        )?;

        // ---- register file: dense positional list ----
        // Positional lookup = ValueMap.get on dense ids
        // (MachineState.lean:51-53). Two-level rec (list outer, Nat inner),
        // the level_eqb shape (kexpr_beq.rs:63).
        self.add_recursive_def(
            r"def ir_regs_get (l : ListType IRValue) (i : Nat) : OptionType IRValue := ListType.rec IRValue (fun (_l : ListType IRValue) => Nat -> OptionType IRValue) (fun (_i : Nat) => OptionType.none IRValue) (fun (h : IRValue) (t : ListType IRValue) (ih : Nat -> OptionType IRValue) => fun (i2 : Nat) => Nat.rec (fun (_n : Nat) => OptionType IRValue) (OptionType.some IRValue h) (fun (p : Nat) (_dead : OptionType IRValue) => ih p) i2) l i",
            "Positional SSA register lookup: index IS the dense ValueId \
             (MachineState.lookupValue, MachineState.lean:51-53). none = SSA \
             violation / missing operand, fail-closed.",
        )?;

        self.add_recursive_def(
            r"def ir_regs_bind (l : ListType IRValue) (v : IRValue) : ListType IRValue := ListType.rec IRValue (fun (_l : ListType IRValue) => ListType IRValue) (ListType.cons IRValue v (ListType.nil IRValue)) (fun (h : IRValue) (t : ListType IRValue) (ih : ListType IRValue) => ListType.cons IRValue h ih) l",
            "Bind a fresh SSA value: append at the end, so the new value's \
             index is the old length — literally MachineState.bindValue \
             (MachineState.lean:56-60) with nextValueId = length.",
        )?;

        // ---- integer binop semantics ----
        self.add_recursive_def(
            r"def ir_binop_eval (op : IRBinOp) (w : Nat) (x : Nat) (y : Nat) : Nat := match op with
| IRBinOp.add => ir_wrap w (Nat.add x y)
| IRBinOp.sub => ir_wrap w (Nat.add x (Nat.sub (ir_nat_pow2 w) y))
| IRBinOp.mul => ir_wrap w (ir_nat_mul x y)",
            "Wrapping width-w integer BinOp on unsigned residues: add/mul mod \
             2^w; sub as x + (2^w - y) mod 2^w (two's-complement subtraction \
             without Int). Mirror of semIntBinOp Add/Sub/Mul \
             (Arith.lean:64-67) per C3 design section 2.2a.",
        )?;

        self.add_recursive_def(
            r"def ir_int_pair_ok (a : IRValue) (b : IRValue) : Bool := Bool.and (Bool.and (ir_val_is_int a) (ir_val_is_int b)) (nat_eqb (ir_val_width a) (ir_val_width b))",
            "Operand admissibility for an integer BinOp: both ints, equal \
             widths — semBinOp's scalar-int guard (Arith.lean:332-333, the \
             width-mismatch type error). The instruction's ty width is NOT \
             consulted, mirroring semBinOp which binds ty and ignores it for \
             scalar ints.",
        )?;

        self.add_recursive_def(
            r"def ir_binop_vals (op : IRBinOp) (a : IRValue) (b : IRValue) : OptionType IRValue := Bool.rec (fun (_g : Bool) => OptionType IRValue) (OptionType.none IRValue) (OptionType.some IRValue (IRValue.intv (ir_val_width a) (ir_binop_eval op (ir_val_width a) (ir_val_num a) (ir_val_num b)))) (ir_int_pair_ok a b)",
            "Apply an integer BinOp to two operand VALUES: some (intv w r) on \
             admissible operands, none (fail-closed) otherwise. The value \
             half of semBinOp's scalar-int arm (Arith.lean:332-336).",
        )?;

        self.add_recursive_def(
            r"def ir_binop_lookup (op : IRBinOp) (ol : OptionType IRValue) (orr : OptionType IRValue) : OptionType IRValue := OptionType.rec IRValue (fun (_o : OptionType IRValue) => OptionType IRValue) (OptionType.none IRValue) (fun (a : IRValue) => OptionType.rec IRValue (fun (_o2 : OptionType IRValue) => OptionType IRValue) (OptionType.none IRValue) (fun (b : IRValue) => ir_binop_vals op a b) orr) ol",
            "Chain the two operand lookups into the BinOp value semantics: \
             any missing operand is none (fail-closed). The Sem.lookupValue \
             sequencing of semBinOp (Arith.lean:314-315) made explicit.",
        )?;

        // ---- lifting produced values into step outcomes ----
        self.add_recursive_def(
            r"def ir_res_next_of (r : ListType IRValue) (o : OptionType IRValue) : OptionType IRStepRes := OptionType.rec IRValue (fun (_o : OptionType IRValue) => OptionType IRStepRes) (OptionType.none IRStepRes) (fun (v : IRValue) => OptionType.some IRStepRes (IRStepRes.next (ir_regs_bind r v))) o",
            "Bind-and-continue: a produced value is appended to the register \
             file (Sem.bindFresh + InstrResult.value, Step.lean:71-73); a \
             failed production stays none, fail-closed.",
        )?;

        self.add_recursive_def(
            r"def ir_res_done_of (o : OptionType IRValue) : OptionType IRStepRes := OptionType.rec IRValue (fun (_o : OptionType IRValue) => OptionType IRStepRes) (OptionType.none IRStepRes) (fun (v : IRValue) => OptionType.some IRStepRes (IRStepRes.done v)) o",
            "Return lifting: a looked-up return value terminates evaluation \
             (semReturn / InstrResult.terminator, Step.lean:202-204); a \
             missing return operand is none, fail-closed.",
        )?;

        // ---- the per-instruction step (stepInst mirror for the slice) ----
        self.add_recursive_def(
            r"def ir_step (i : IRInst) (r : ListType IRValue) : OptionType IRStepRes := match i with
| IRInst.iconst w v => OptionType.some IRStepRes (IRStepRes.next (ir_regs_bind r (IRValue.intv w (ir_wrap w v))))
| IRInst.ibinop op w l rr => ir_res_next_of r (ir_binop_lookup op (ir_regs_get r l) (ir_regs_get r rr))
| IRInst.iret vid => ir_res_done_of (ir_regs_get r vid)",
            "EvalIR single-instruction step (the stepInst mirror for the \
             wave-1 slice, Step.lean:68/98/71/202): iconst binds a fresh \
             in-range constant (reduced mod 2^w at binding, identity on the \
             producer's in-range emissions — C3 design section 3.2); ibinop \
             looks up both operands and applies the wrapping op (the ty width \
             field is carried for Inst::BinOp fidelity and not consulted, \
             mirroring semBinOp); iret returns the looked-up value. Every \
             non-modelled/ill-formed configuration is none, fail-closed.",
        )?;

        // ---- the fuel loop (whnf_fuel_red idiom / stepN mirror) ----
        self.add_recursive_def(
            r"def ir_dispatch (o : OptionType IRStepRes) (rest : ListType IRInst) (ih : ListType IRInst -> ListType IRValue -> OptionType IRValue) : OptionType IRValue := OptionType.rec IRStepRes (fun (_o : OptionType IRStepRes) => OptionType IRValue) (OptionType.none IRValue) (fun (sr : IRStepRes) => IRStepRes.rec (fun (_s : IRStepRes) => OptionType IRValue) (fun (r2 : ListType IRValue) => ih rest r2) (fun (v : IRValue) => OptionType.some IRValue v) sr) o",
            "EvalIR loop dispatch: a stuck step is none; next r2 continues on \
             the rest of the program via the fuel IH; done v is the final \
             verdict. The loop_dispatch shape of the 3-way whnf loop \
             (whnf_progress.rs:562) specialized to straight-line programs.",
        )?;

        self.add_recursive_def(
            r"def ir_eval_fuel (fuel : Nat) (p : ListType IRInst) (r : ListType IRValue) : OptionType IRValue := Nat.rec (fun (_k : Nat) => ListType IRInst -> ListType IRValue -> OptionType IRValue) (fun (_p : ListType IRInst) (_r : ListType IRValue) => OptionType.none IRValue) (fun (k : Nat) (ih : ListType IRInst -> ListType IRValue -> OptionType IRValue) => fun (p2 : ListType IRInst) (r2 : ListType IRValue) => ListType.rec IRInst (fun (_l : ListType IRInst) => OptionType IRValue) (OptionType.none IRValue) (fun (i : IRInst) (rest : ListType IRInst) (_dead : OptionType IRValue) => ir_dispatch (ir_step i r2) rest ih) p2) fuel p r",
            "EvalIR fuel-bounded straight-line evaluator (the whnf_fuel_red \
             idiom, whnf_progress.rs:562; the stepN mirror, \
             Eval.lean:135-152): none is the honest fuel bail AND the \
             fail-closed stuck verdict (conflated this slice — C3 design \
             section 4 deviation 4); some v means one instruction per fuel \
             unit ran to an iret returning v. Falling off the program end \
             without a terminator is none (a block must end in a \
             terminator).",
        )?;

        Ok(())
    }

    /// Non-vacuity witnesses (design §6): concrete programs the kernel's
    /// defeq must EXECUTE through `ir_eval_fuel` to accept each `Eq.refl`.
    /// Width 2 throughout (`2^w = 4`) so every reduction is a few dozen
    /// kernel steps.
    fn add_evalir_witnesses(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def irRegsNil : ListType IRValue := ListType.nil IRValue",
            "Empty register file for witness programs. EvalIR witnesses.",
        )?;

        // [iconst 2 1, iret 0] -- Const then Return.
        self.add_recursive_def(
            r"def irProgConstRet : ListType IRInst := ListType.cons IRInst (IRInst.iconst (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iret Nat.zero) (ListType.nil IRInst))",
            "Witness program: [iconst w=2 v=1; iret 0]. EvalIR witnesses.",
        )?;

        self.add_recursive_def(
            r"def ir_witness_const_ret : Eq (OptionType IRValue) (ir_eval_fuel (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) irProgConstRet irRegsNil) (OptionType.some IRValue (IRValue.intv (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero))) := Eq.refl (OptionType IRValue) (OptionType.some IRValue (IRValue.intv (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)))",
            "NON-VACUITY (Const+Return): [iconst 2 1; iret 0] at fuel 4 \
             evaluates to some (intv 2 1). The kernel's defeq runs the \
             evaluator to close this refl — an execution, not a restatement. \
             EvalIR witnesses.",
        )?;

        // [iconst 2 1, iconst 2 2, ibinop add _ 0 1, iret 2] => 1+2 = 3.
        self.add_recursive_def(
            r"def irProgAdd : ListType IRInst := ListType.cons IRInst (IRInst.iconst (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iconst (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))) (ListType.cons IRInst (IRInst.ibinop IRBinOp.add (Nat.succ (Nat.succ Nat.zero)) Nat.zero (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iret (Nat.succ (Nat.succ Nat.zero))) (ListType.nil IRInst))))",
            "Witness program: [iconst 2 1; iconst 2 2; ibinop add %0 %1; \
             iret %2]. EvalIR witnesses.",
        )?;

        self.add_recursive_def(
            r"def ir_witness_add : Eq (OptionType IRValue) (ir_eval_fuel (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) irProgAdd irRegsNil) (OptionType.some IRValue (IRValue.intv (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) := Eq.refl (OptionType IRValue) (OptionType.some IRValue (IRValue.intv (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))",
            "NON-VACUITY (BinOp add): 1 + 2 at width 2 evaluates to \
             some (intv 2 3) at fuel 6. EvalIR witnesses.",
        )?;

        // [iconst 2 1, iconst 2 3, ibinop sub _ 0 1, iret 2] => 1-3 wraps to 2.
        self.add_recursive_def(
            r"def irProgSubWrap : ListType IRInst := ListType.cons IRInst (IRInst.iconst (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iconst (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (ListType.cons IRInst (IRInst.ibinop IRBinOp.sub (Nat.succ (Nat.succ Nat.zero)) Nat.zero (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iret (Nat.succ (Nat.succ Nat.zero))) (ListType.nil IRInst))))",
            "Witness program: [iconst 2 1; iconst 2 3; ibinop sub %0 %1; \
             iret %2] — 1 - 3 must WRAP. EvalIR witnesses.",
        )?;

        self.add_recursive_def(
            r"def ir_witness_sub_wraps : Eq (OptionType IRValue) (ir_eval_fuel (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) irProgSubWrap irRegsNil) (OptionType.some IRValue (IRValue.intv (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)))) := Eq.refl (OptionType IRValue) (OptionType.some IRValue (IRValue.intv (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))))",
            "NON-VACUITY (BinOp sub, wrapping): 1 - 3 at width 2 evaluates to \
             some (intv 2 2) — truncated Nat.sub would give 0; the result 2 \
             witnesses the two's-complement path (1 + (4-3)) mod 4 genuinely \
             firing (semIntBinOp Sub mirror, Arith.lean:66). EvalIR \
             witnesses.",
        )?;

        // [iconst 2 2, iconst 2 3, ibinop mul _ 0 1, iret 2] => 6 mod 4 = 2.
        self.add_recursive_def(
            r"def irProgMulWrap : ListType IRInst := ListType.cons IRInst (IRInst.iconst (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))) (ListType.cons IRInst (IRInst.iconst (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (ListType.cons IRInst (IRInst.ibinop IRBinOp.mul (Nat.succ (Nat.succ Nat.zero)) Nat.zero (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iret (Nat.succ (Nat.succ Nat.zero))) (ListType.nil IRInst))))",
            "Witness program: [iconst 2 2; iconst 2 3; ibinop mul %0 %1; \
             iret %2] — 2 * 3 = 6 must reduce mod 4. EvalIR witnesses.",
        )?;

        self.add_recursive_def(
            r"def ir_witness_mul_wraps : Eq (OptionType IRValue) (ir_eval_fuel (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) irProgMulWrap irRegsNil) (OptionType.some IRValue (IRValue.intv (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)))) := Eq.refl (OptionType IRValue) (OptionType.some IRValue (IRValue.intv (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))))",
            "NON-VACUITY (BinOp mul, wrapping): 2 * 3 at width 2 evaluates to \
             some (intv 2 2) = 6 mod 4 — witnesses the modulus genuinely \
             firing. EvalIR witnesses.",
        )?;

        // Fail-closed: binop on an empty register file is none.
        self.add_recursive_def(
            r"def irProgMissingOperand : ListType IRInst := ListType.cons IRInst (IRInst.ibinop IRBinOp.add (Nat.succ (Nat.succ Nat.zero)) Nat.zero (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iret Nat.zero) (ListType.nil IRInst))",
            "Witness program: [ibinop add %0 %1; iret %0] with NO bound \
             registers — must be stuck. EvalIR witnesses.",
        )?;

        self.add_recursive_def(
            r"def ir_witness_missing_operand_stuck : Eq (OptionType IRValue) (ir_eval_fuel (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) irProgMissingOperand irRegsNil) (OptionType.none IRValue) := Eq.refl (OptionType IRValue) (OptionType.none IRValue)",
            "FAIL-CLOSED witness: a BinOp whose operands are unbound (SSA \
             violation) evaluates to none, never a default value. EvalIR \
             witnesses.",
        )?;

        // Fail-closed: width mismatch (intv 2 _ + intv 1 _) is none.
        self.add_recursive_def(
            r"def irProgWidthMismatch : ListType IRInst := ListType.cons IRInst (IRInst.iconst (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iconst (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.ibinop IRBinOp.add (Nat.succ (Nat.succ Nat.zero)) Nat.zero (Nat.succ Nat.zero)) (ListType.cons IRInst (IRInst.iret (Nat.succ (Nat.succ Nat.zero))) (ListType.nil IRInst))))",
            "Witness program: width-2 constant + width-1 constant — operand \
             width mismatch must be stuck (semBinOp's width type error, \
             Arith.lean:333). EvalIR witnesses.",
        )?;

        self.add_recursive_def(
            r"def ir_witness_width_mismatch_stuck : Eq (OptionType IRValue) (ir_eval_fuel (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) irProgWidthMismatch irRegsNil) (OptionType.none IRValue) := Eq.refl (OptionType IRValue) (OptionType.none IRValue)",
            "FAIL-CLOSED witness: mismatched operand widths evaluate to none \
             (the semBinOp width type error mirrored, Arith.lean:332-333). \
             EvalIR witnesses.",
        )?;

        // Honest fuel bail: fuel 0 is none even on a good program.
        self.add_recursive_def(
            r"def ir_witness_fuel_zero_bails : Eq (OptionType IRValue) (ir_eval_fuel Nat.zero irProgConstRet irRegsNil) (OptionType.none IRValue) := Eq.refl (OptionType IRValue) (OptionType.none IRValue)",
            "FUEL-BAIL witness: fuel 0 on a well-formed program is none — the \
             honest bail of the whnf_fuel_red idiom (stepN outOfFuel mirror, \
             Eval.lean:142-143). EvalIR witnesses.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::spec::Specification;

    /// Build the EvalIR decls on the Substitution test bundle — foundation
    /// (Nat/Bool/Eq/ProdType) + expr_model (ListType) + rec_env (OptionType,
    /// nat_eqb) — exactly the substrate the live wiring will provide, without
    /// touching the shared stage list (same pattern as
    /// `kexpr_beq.rs::tests::build_kexpr_beq_spec`).
    fn build_evalir_spec() -> Specification {
        let mut spec = Specification::new_substitution_test_spec()
            .expect("substitution-test spec (foundation + expr_model + rec_env) should build");
        spec.add_evalir()
            .expect("EvalIR decls should elaborate and kernel-check");
        spec
    }

    /// Every EvalIR declaration registers and kernel-checks. `add_evalir`
    /// returning Ok already means every def/witness passed full
    /// `env.add_decl` kernel type-checking — in particular each `Eq.refl`
    /// witness forced the kernel's defeq to RUN the evaluator.
    #[test]
    fn test_evalir_decls_kernel_check() {
        let spec = build_evalir_spec();
        let defs = spec.definitions();

        for name in [
            // substrate
            "ir_nat_mul",
            "ir_nat_pow2",
            "ir_nat_mod",
            "ir_wrap",
            // domain operations
            "ir_heap_get",
            "ir_val_is_int",
            "ir_val_width",
            "ir_val_num",
            "ir_regs_get",
            "ir_regs_bind",
            // semantics
            "ir_binop_eval",
            "ir_int_pair_ok",
            "ir_binop_vals",
            "ir_binop_lookup",
            "ir_res_next_of",
            "ir_res_done_of",
            "ir_step",
            "ir_dispatch",
            "ir_eval_fuel",
        ] {
            assert!(
                defs.contains_key(name),
                "EvalIR def {name} should be registered"
            );
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
                "EvalIR def {name} should be in the kernel environment"
            );
        }

        // The inductives live in the kernel environment.
        for name in ["IRValue", "IRBinOp", "IRInst", "IRStepRes"] {
            assert!(
                spec.env()
                    .get_inductive(&clean_kernel::Name::from_string(name))
                    .is_some(),
                "EvalIR inductive {name} should be in the kernel environment"
            );
        }
    }

    /// The non-vacuity witnesses are present and none is an axiom: each
    /// carries a value (`Eq.refl` at the computed verdict) that the kernel
    /// accepted, i.e. the evaluator genuinely computes the stated results —
    /// including the two fail-closed verdicts and the fuel bail.
    #[test]
    fn test_evalir_witnesses_are_valued_executions() {
        let spec = build_evalir_spec();
        let defs = spec.definitions();

        for name in [
            "ir_witness_const_ret",
            "ir_witness_add",
            "ir_witness_sub_wraps",
            "ir_witness_mul_wraps",
            "ir_witness_missing_operand_stuck",
            "ir_witness_width_mismatch_stuck",
            "ir_witness_fuel_zero_bails",
        ] {
            let def = defs
                .get(name)
                .unwrap_or_else(|| panic!("witness {name} should be registered"));
            assert!(!def.is_axiom, "witness {name} must not be an axiom");
            assert!(
                def.elaborated_value.is_some(),
                "witness {name} must carry its kernel-checked Eq.refl value"
            );
            assert!(
                def.axiom_deps.is_empty(),
                "witness {name} must have an empty axiom closure, got {:?}",
                def.axiom_deps
            );
        }
    }
}
