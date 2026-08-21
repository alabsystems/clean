// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — machine transitions, the 28-arm dispatch, and the driver (**C3**).
//!
//! `ir_exec` is the coverage claim of this job: **one arm per constructed
//! `Inst` variant, 28 of 28**, each a single flat call into a helper defined
//! here or in [`super::eval_ir_ops`]. `ir_step` fetches a node; `ir_run`
//! iterates on fuel; `ir_eval` is the entry point a theorem states an equality
//! about.
//!
//! Two design points worth stating once, because both are places where being
//! faithful to the Rust IR costs something:
//!
//! - **Result ids come from the node, not from a counter.** `trust_ir`'s
//!   `InstrNode` declares `results : Vec<ValueId>`, so the machine has no
//!   fresh-id counter at all. See the `IRNode` registration in
//!   [`super::eval_ir_syntax`] for why the Lean reference's `bindFresh` could
//!   not be copied here.
//! - **Recursion is ordinary frame stacking.** `ir_call_exec` pushes,
//!   `ir_return_exec` pops and binds the returns positionally into the caller's
//!   declared result ids. That is load-bearing rather than
//!   forward-compatibility: the crystal target `Level::is_zero` recurses on its
//!   `Max` and `IMax` arms.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Register the machine layer.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_machine(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_projections()?;
        self.add_eval_ir_transitions()?;
        self.add_eval_ir_memory()?;
        self.add_eval_ir_aggregates()?;
        self.add_eval_ir_control()?;
        self.add_eval_ir_dispatch()
    }

    /// Field projections and SSA lookup.
    fn add_eval_ir_projections(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def ir_frame_func (f : IRFrame) : Nat := match f with
| IRFrame.mk fnid bl pc loc ds => fnid",
            "The function id of a frame.",
        )?;
        self.add_recursive_def(
            r"def ir_frame_block (f : IRFrame) : Nat := match f with
| IRFrame.mk fnid bl pc loc ds => bl",
            "The current block id of a frame.",
        )?;
        self.add_recursive_def(
            r"def ir_frame_pc (f : IRFrame) : Nat := match f with
| IRFrame.mk fnid bl pc loc ds => pc",
            "The program counter of a frame.",
        )?;
        self.add_recursive_def(
            r"def ir_frame_locals (f : IRFrame) : IRList IRBinding := match f with
| IRFrame.mk fnid bl pc loc ds => loc",
            "The locals of a frame.",
        )?;
        self.add_recursive_def(
            r"def ir_frame_dests (f : IRFrame) : IRList Nat := match f with
| IRFrame.mk fnid bl pc loc ds => ds",
            "The caller's declared result ids for this frame's return values.",
        )?;

        self.add_recursive_def(
            r"def ir_mach_frames (s : IRMachine) : IRList IRFrame := match s with
| IRMachine.mk fs mem na => fs",
            "The frame stack.",
        )?;
        self.add_recursive_def(
            r"def ir_mach_mem (s : IRMachine) : IRList IRMemSlot := match s with
| IRMachine.mk fs mem na => mem",
            "The memory.",
        )?;

        self.add_recursive_def(
            r"def ir_block_params (b : IRBlock) : IRList Nat := match b with
| IRBlock.mk i ps nodes => ps",
            "The block parameters bound on entry from a predecessor's branch arguments.",
        )?;
        self.add_recursive_def(
            r"def ir_block_nodes (b : IRBlock) : IRList IRNode := match b with
| IRBlock.mk i ps nodes => nodes",
            "The nodes of a block.",
        )?;
        self.add_recursive_def(
            r"def ir_func_blocks (f : IRFunc) : IRList IRBlock := match f with
| IRFunc.mk i ps entry bs => bs",
            "The blocks of a function.",
        )?;
        self.add_recursive_def(
            r"def ir_func_entry (f : IRFunc) : Nat := match f with
| IRFunc.mk i ps entry bs => entry",
            "The entry block of a function.",
        )?;
        self.add_recursive_def(
            r"def ir_func_id (f : IRFunc) : Nat := match f with
| IRFunc.mk i ps entry bs => i",
            "The id of a function.",
        )?;
        self.add_recursive_def(
            r"def ir_func_params (f : IRFunc) : IRList Nat := match f with
| IRFunc.mk i ps entry bs => ps",
            "The parameters of a function.",
        )?;
        self.add_recursive_def(
            r"def ir_mod_funcs (m : IRModule) : IRList IRFunc := match m with
| IRModule.mk fs gs => fs",
            "The functions of a module.",
        )?;
        self.add_recursive_def(
            r"def ir_mod_globals (m : IRModule) : IRList IRGlobal := match m with
| IRModule.mk fs gs => gs",
            "The globals of a module.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_opt_value (o : IROption IRScalar) : IRScalar := ",
                "IROption.rec IRScalar (fun (_ : IROption IRScalar) => IRScalar) ",
                "IRScalar.undef_ (fun (v : IRScalar) => v) o",
            ),
            "An unbound SSA id reads as undef_ rather than getting stuck. Every instruction that \
             needs a real value rejects undef_ explicitly (loading it is UB, using it as a \
             pointer or a condition is a type_error), so the default cannot silently succeed.",
        )?;

        self.add_recursive_def(
            "def ir_frame_get (f : IRFrame) (k : Nat) : IRScalar := ir_opt_value (ir_binding_lookup (ir_frame_locals f) k)",
            "Read an SSA value in a frame.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_frames_get (fs : IRList IRFrame) (k : Nat) : IRScalar := ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRScalar) IRScalar.undef_ ",
                "(fun (f : IRFrame) (_ : IRList IRFrame) (_ : IRScalar) => ir_frame_get f k) fs",
            ),
            "Read an SSA value in the CURRENT frame only. A callee cannot see its caller's \
             bindings — SSA scoping is per function, and this is what enforces it.",
        )?;

        self.add_recursive_def(
            "def ir_getd (s : IRMachine) (k : Nat) : IRScalar := ir_frames_get (ir_mach_frames s) k",
            "Read an SSA value in the machine's current frame.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_resolve (s : IRMachine) (ids : IRList Nat) : IRList IRScalar := ",
                "IRList.rec Nat (fun (_ : IRList Nat) => IRList IRScalar) (IRList.nil IRScalar) ",
                "(fun (i : Nat) (_ : IRList Nat) (ih : IRList IRScalar) => ",
                "IRList.cons IRScalar (ir_getd s i) ih) ids",
            ),
            "Resolve an argument id list to values, in order.",
        )?;

        Ok(())
    }

    /// Frame and machine transitions.
    fn add_eval_ir_transitions(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_bind_params (ps : IRList Nat) (vs : IRList IRScalar) (loc : IRList IRBinding) : IRList IRBinding := ",
                "IRList.rec Nat (fun (_ : IRList Nat) => IRList IRScalar -> IRList IRBinding) ",
                "(fun (_ : IRList IRScalar) => loc) ",
                "(fun (p : Nat) (_ : IRList Nat) (ih : IRList IRScalar -> IRList IRBinding) => ",
                "fun (ws : IRList IRScalar) => ",
                "IRList.rec IRScalar (fun (_ : IRList IRScalar) => IRList IRBinding) ",
                "loc ",
                "(fun (w : IRScalar) (wrest : IRList IRScalar) (_ : IRList IRBinding) => ",
                "IRList.cons IRBinding (IRBinding.mk p w) (ih wrest)) ",
                "ws) ",
                "ps vs",
            ),
            "Bind an id list to a value list, positionally, on top of an existing locals list. \
             Three callers all want exactly this: function parameters at a call, block parameters \
             at a branch, and a node's declared results. A length mismatch binds the common prefix \
             and stops — arity is producer-side well-formedness that validate_module checks, not \
             something to re-litigate on every step.",
        )?;

        self.add_recursive_def(
            r"def ir_frame_bind (f : IRFrame) (rs : IRList Nat) (v : IRScalar) : IRFrame := match f with
| IRFrame.mk fnid bl pc loc ds => IRFrame.mk fnid bl (Nat.succ pc) (ir_bind_params rs (IRList.cons IRScalar v (IRList.nil IRScalar)) loc) ds",
            "Bind a value-producing instruction's single result to the FIRST id the node declares, \
             and advance past it. A node with an empty result list evaluates the instruction and \
             discards the value, which is what an unused result means.",
        )?;

        self.add_recursive_def(
            r"def ir_frame_set_many (f : IRFrame) (rs : IRList Nat) (vs : IRList IRScalar) : IRFrame := match f with
| IRFrame.mk fnid bl pc loc ds => IRFrame.mk fnid bl pc (ir_bind_params rs vs loc) ds",
            "Bind several values WITHOUT advancing: the return path. The caller's program counter \
             was already advanced when the call was pushed, and a multi-value return binds \
             positionally to the call node's declared result ids.",
        )?;

        self.add_recursive_def(
            r"def ir_frame_advance (f : IRFrame) : IRFrame := match f with
| IRFrame.mk fnid bl pc loc ds => IRFrame.mk fnid bl (Nat.succ pc) loc ds",
            "Advance past an instruction that binds nothing (Store, Assert, and the caller side \
             of a Call).",
        )?;

        self.add_recursive_def(
            r"def ir_frame_goto (f : IRFrame) (blk : Nat) (bs : IRList IRBinding) : IRFrame := match f with
| IRFrame.mk fnid bl pc loc ds => IRFrame.mk fnid blk Nat.zero bs ds",
            "Transfer control to a block: new block id, program counter zero, new locals.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_bind (s : IRMachine) (rs : IRList Nat) (v : IRScalar) : IRConfig := ",
                "IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(IRList.cons IRFrame (ir_frame_bind f rs v) rest) mem na)) ",
                "fs) s",
            ),
            "Bind a result at the ids the current node declares, and advance.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_bind_result (s : IRMachine) (rs : IRList Nat) (r : IRStepResult) : IRConfig := ",
                "IRStepResult.rec (fun (_ : IRStepResult) => IRConfig) ",
                "(fun (v : IRScalar) => ir_bind s rs v) ",
                "(fun (o : IROutcome) => IRConfig.halted o) r",
            ),
            "Bind a value-level evaluator's result, or halt on its fault.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_advance (s : IRMachine) : IRConfig := ",
                "IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(IRList.cons IRFrame (ir_frame_advance f) rest) mem na)) ",
                "fs) s",
            ),
            "Advance past a value-less instruction.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_set_mem (s : IRMachine) (m2 : IRList IRMemSlot) : IRMachine := ",
                "IRMachine.rec (fun (_ : IRMachine) => IRMachine) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "IRMachine.mk fs m2 na) s",
            ),
            "Replace the memory.",
        )?;

        Ok(())
    }

    /// Load, Store, Alloca, GEP and the pointer-lane instructions.
    fn add_eval_ir_memory(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def ir_load_value (v : IRScalar) : IRStepResult := match v with
| IRScalar.undef_ => IRStepResult.fault (IROutcome.ub IRFault.uninit)
| IRScalar.bool_ b => IRStepResult.value (IRScalar.bool_ b)
| IRScalar.int_ n => IRStepResult.value (IRScalar.int_ n)
| IRScalar.float_ n => IRStepResult.value (IRScalar.float_ n)
| IRScalar.unit_ => IRStepResult.value IRScalar.unit_
| IRScalar.ptr_ a => IRStepResult.value (IRScalar.ptr_ a)
| IRScalar.nullptr_ => IRStepResult.value IRScalar.nullptr_
| IRScalar.fat_ d md => IRStepResult.value (IRScalar.fat_ d md)
| IRScalar.fnptr_ f => IRStepResult.value (IRScalar.fnptr_ f)
| IRScalar.aggv sp => IRStepResult.value (IRScalar.aggv sp)
| IRScalar.vnil => IRStepResult.value IRScalar.vnil
| IRScalar.vcons x rest => IRStepResult.value (IRScalar.vcons x rest)",
            "The contents of a live cell, as a load result. Reading a cell that was never written \
             is UB — the Lean model's 'reading uninitialized memory'. THE AGGREGATE CASE IS THE \
             WHOLE POINT: loading an inline aggregate value needs no byte size, which is exactly \
             what Ty.byteSize's `Enum => none` denies the Lean semantics. Load is the identity on \
             every non-undef_ value, including a bare spine cell, which is representable but \
             meaningless; that costs nothing, because every consumer of a loaded value rejects the \
             spine constructors with its own type_error.",
        )?;

        self.add_recursive_def(
            r"def ir_load_cell (s : IRMemSlot) : IRStepResult := match s with
| IRMemSlot.mk a v live => Bool.rec (fun (_ : Bool) => IRStepResult) (IRStepResult.fault (IROutcome.ub IRFault.bad_addr)) (ir_load_value v) live",
            "Load from a cell, refusing a dead one. Bool.rec minor order is (false, true), so the \
             first minor is the dead case.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_load_slot (o : IROption IRMemSlot) : IRStepResult := ",
                "IROption.rec IRMemSlot (fun (_ : IROption IRMemSlot) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.bad_addr)) ",
                "(fun (s : IRMemSlot) => ir_load_cell s) o",
            ),
            "An address with no cell is out of bounds — UB, not a stuck state.",
        )?;

        self.add_recursive_def(
            r"def ir_load_at (mem : IRList IRMemSlot) (p : IRScalar) : IRStepResult := match p with
| IRScalar.undef_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => ir_load_slot (ir_mem_lookup mem a)
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.ub IRFault.null_deref)
| IRScalar.fat_ d md => ir_load_slot (ir_mem_lookup mem d)
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "Load through a pointer. Dereferencing null is UB: that is the panic arm the crystal's \
             LevelArc deref carries, since LevelArc is Option<Arc<Level>> whose Deref expects Some \
             and whose None state exists only mid-Drop.",
        )?;

        self.add_recursive_def(
            "def ir_load_eval (s : IRMachine) (p : IRScalar) : IRStepResult := ir_load_at (ir_mach_mem s) p",
            "Load through a pointer in the machine's memory.",
        )?;

        self.add_recursive_def(
            r"def ir_slot_live (s : IRMemSlot) : Bool := match s with
| IRMemSlot.mk a v live => live",
            "Liveness of a cell.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_store_live (s : IRMachine) (a : Nat) (v : IRScalar) (live : Bool) : IRConfig := ",
                "Bool.rec (fun (_ : Bool) => IRConfig) ",
                "(IRConfig.halted (IROutcome.ub IRFault.bad_addr)) ",
                "(ir_advance (ir_set_mem s (ir_mem_update (ir_mach_mem s) a v))) ",
                "live",
            ),
            "Commit a store to a live cell.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_store_checked (s : IRMachine) (a : Nat) (v : IRScalar) (o : IROption IRMemSlot) : IRConfig := ",
                "IROption.rec IRMemSlot (fun (_ : IROption IRMemSlot) => IRConfig) ",
                "(IRConfig.halted (IROutcome.ub IRFault.bad_addr)) ",
                "(fun (c : IRMemSlot) => ir_store_live s a v (ir_slot_live c)) o",
            ),
            "Storing to an address with no cell is out-of-bounds UB.",
        )?;

        self.add_recursive_def(
            r"def ir_store_exec (s : IRMachine) (p : IRScalar) (v : IRScalar) : IRConfig := match p with
| IRScalar.undef_ => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)
| IRScalar.bool_ b => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => ir_store_checked s a v (ir_mem_lookup (ir_mach_mem s) a)
| IRScalar.nullptr_ => IRConfig.halted (IROutcome.ub IRFault.null_deref)
| IRScalar.fat_ d md => ir_store_checked s d v (ir_mem_lookup (ir_mach_mem s) d)
| IRScalar.fnptr_ f => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRConfig.halted (IROutcome.type_error IRFault.not_ptr)",
            "Store through a pointer.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_alloc_cells (base : Nat) (k : Nat) (mem : IRList IRMemSlot) : IRList IRMemSlot := ",
                "Nat.rec (fun (_ : Nat) => IRList IRMemSlot) mem ",
                "(fun (j : Nat) (ih : IRList IRMemSlot) => ",
                "IRList.cons IRMemSlot (IRMemSlot.mk (Nat.add base j) IRScalar.undef_ Bool.true) ih) k",
            ),
            "Create k live, uninitialised cells at base .. base+k-1. Uninitialised is undef_, and \
             loading undef_ is UB, so an unwritten allocation cannot be read as a value.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_alloca_k (s : IRMachine) (rs : IRList Nat) (k : Nat) : IRConfig := ",
                "IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(IRList.cons IRFrame (ir_frame_bind f rs (IRScalar.ptr_ na)) rest) ",
                "(ir_alloc_cells na k mem) (Nat.add na k))) ",
                "fs) s",
            ),
            "Allocate k cells and bind a pointer to the first. The address counter only ever \
             grows, so an address is never reused and a stale pointer never aliases a new \
             allocation.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_alloca_count (s : IRMachine) (c : IROption Nat) : IROption Nat := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) ",
                "(IROption.some Nat (Nat.succ Nat.zero)) ",
                "(fun (i : Nat) => ir_as_int (ir_getd s i)) c",
            ),
            "Alloca's element count: absent means one, present means the integer value of that \
             SSA operand.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_alloca_exec (s : IRMachine) (rs : IRList Nat) (c : IROption Nat) : IRConfig := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_int)) ",
                "(fun (k : Nat) => ir_alloca_k s rs k) (ir_alloca_count s c)",
            ),
            "Alloca.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_opt_add (a : IROption Nat) (b : IROption Nat) : IROption Nat := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) (IROption.none Nat) ",
                "(fun (x : Nat) => IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) ",
                "(IROption.none Nat) (fun (y : Nat) => IROption.some Nat (Nat.add x y)) b) a",
            ),
            "Addition lifted over partiality, for GEP's index sum.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_sum_idx (l : IRList IRScalar) : IROption Nat := ",
                "IRList.rec IRScalar (fun (_ : IRList IRScalar) => IROption Nat) ",
                "(IROption.some Nat Nat.zero) ",
                "(fun (x : IRScalar) (_ : IRList IRScalar) (ih : IROption Nat) => ",
                "ir_opt_add (ir_as_int x) ih) l",
            ),
            "Sum of GEP's indices. trust-ir GEP is SINGLE-SCALE array indexing — \
             base + (sum of indices) * size_of(pointee), not LLVM's type-walking multi-scale GEP \
             — and in a cell-addressed model size_of(pointee) is one cell, so the scale is one. \
             Struct field access is ExtractField, never a nested GEP index; that is the producer's \
             documented rule, not a simplification taken here.",
        )?;

        self.add_recursive_def(
            r"def ir_gep_base (base : IRScalar) (off : Nat) : IRStepResult := match base with
| IRScalar.undef_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => IRStepResult.value (IRScalar.ptr_ (Nat.add a off))
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.ub IRFault.null_deref)
| IRScalar.fat_ d md => IRStepResult.value (IRScalar.fat_ (Nat.add d off) md)
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "Offset a pointer. There is no negative index: the index type is Nat, so trust-ir \
             GEP's 'a negative index is UB' rule holds by unrepresentability.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_gep_eval (base : IRScalar) (idxs : IRList IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (off : Nat) => ir_gep_base base off) (ir_sum_idx idxs)",
            ),
            "GEP.",
        )?;

        self.add_recursive_def(
            r"def ir_ptrdata_eval (p : IRScalar) : IRStepResult := match p with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => IRStepResult.value (IRScalar.ptr_ a)
| IRScalar.nullptr_ => IRStepResult.value IRScalar.nullptr_
| IRScalar.fat_ d md => IRStepResult.value (IRScalar.ptr_ d)
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "PtrData: the data lane. Identity on a thin pointer (provenance-preserving), the data \
             half of a wide one.",
        )?;

        self.add_recursive_def(
            r"def ir_ptrmeta_eval (p : IRScalar) : IRStepResult := match p with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => IRStepResult.value IRScalar.unit_
| IRScalar.nullptr_ => IRStepResult.value IRScalar.unit_
| IRScalar.fat_ d md => IRStepResult.value (IRScalar.int_ md)
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "PtrMetadata: unit for a thin pointer, the metadata word for a wide one — the \
             thin-vs-fat dispatch that is why IRTy keeps its pointee.",
        )?;

        self.add_recursive_def(
            r"def ir_ptrparts_at (a : Nat) (md : IRScalar) : IRStepResult := match md with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRScalar.int_ n => IRStepResult.value (IRScalar.fat_ a n)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRScalar.unit_ => IRStepResult.value (IRScalar.ptr_ a)
| IRScalar.ptr_ x => IRStepResult.value (IRScalar.fat_ a x)
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRScalar.fat_ d m2 => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRScalar.fnptr_ f => IRStepResult.value (IRScalar.fat_ a f)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_int)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_int)",
            "PtrFromParts at a resolved data address: unit metadata rebuilds a thin pointer, an \
             integer rebuilds a slice/str wide pointer, and a pointer or function pointer rebuilds \
             a trait-object wide pointer (vtable metadata is a thin pointer).",
        )?;

        self.add_recursive_def(
            r"def ir_ptrparts_eval (d : IRScalar) (md : IRScalar) : IRStepResult := match d with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => ir_ptrparts_at a md
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.ub IRFault.null_deref)
| IRScalar.fat_ x m2 => ir_ptrparts_at x md
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "PtrFromParts.",
        )?;

        Ok(())
    }

    /// ExtractField, InsertField, ExtractElement over inline aggregate values.
    fn add_eval_ir_aggregates(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_field_result (o : IROption IRScalar) : IRStepResult := ",
                "IROption.rec IRScalar (fun (_ : IROption IRScalar) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.bad_field)) ",
                "(fun (v : IRScalar) => IRStepResult.value v) o",
            ),
            "A field read, or bad_field if the index is out of range.",
        )?;

        self.add_recursive_def(
            r"def ir_ef_at (a : IRScalar) (k : Nat) : IRStepResult := match a with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.ptr_ x => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.fat_ d md => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.aggv sp => ir_field_result (ir_vals_get sp k)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)",
            "ExtractField: the operand must be an aggregate VALUE, not a pointer to one — reading \
             through a pointer is Load, exactly as in trust-ir. Index k is spine slot k, \
             uniformly; for an enum that makes slot 0 the discriminant and slot (succ j) payload \
             field j, which is the trust-ir producer's tag-at-field-0 convention rather than a \
             special case in the semantics. ExtractField is now machine-independent: it is a pure \
             function of the value.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_extract_elem (a : IRScalar) (kv : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_int)) ",
                "(fun (k : Nat) => ir_ef_at a k) (ir_as_int kv)",
            ),
            "ExtractElement: an array element read at a computed index. It is exactly \
             ExtractField at that index — under the inline encoding there is no record/variant \
             split, so an array's element k is spine slot k with no discriminant offset to \
             correct for.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_if_at (sp : IRScalar) (k : Nat) (v : IRScalar) : IRStepResult := ",
                "Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.bad_field)) ",
                "(IRStepResult.value (IRScalar.aggv (ir_vals_set sp k v))) ",
                "(ir_nat_ltb k (ir_vals_len sp))",
            ),
            "Field write into an aggregate's spine, rebuilding the whole value. Bool.rec minor \
             order is (false, true), so the FIRST minor is the out-of-range case — which \
             preserves the fault order of the design this replaced: a non-aggregate operand is \
             decided by ir_insert_field's outer match (not_agg) BEFORE the index is examined \
             (bad_field). Values are immutable, so the rewritten copy cannot disturb the original \
             — every value already read out of memory still denotes what it denoted.",
        )?;

        self.add_recursive_def(
            r"def ir_insert_field (a : IRScalar) (k : Nat) (v : IRScalar) : IRStepResult := match a with
| IRScalar.undef_ => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.ptr_ x => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.fat_ d md => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.aggv sp => ir_if_at sp k v
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_agg)",
            "InsertField, as an ordinary value-producing evaluator: it is a pure function of the \
             value, so it goes through ir_bind_result like every other producer. RECORDED \
             BEHAVIOUR CHANGE: index 0 of an enum is an ordinary field write and accepts any \
             value, where a discriminant-lane special case would run ir_as_int on it and fault \
             with bad_field on a non-integer. That is the price of having no special case at all, \
             and it agrees with the producer, whose tag lane IS field 0 of an ordinary aggregate. \
             Index 0 is bounds-checked like any other: every enum value carries its tag, so its \
             spine length is at least one, and a zero-field aggregate fails the write.",
        )?;

        Ok(())
    }

    /// Branches, switch, calls, returns, assert, select, global addresses.
    fn add_eval_ir_control(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_goto (s : IRMachine) (tgt : Nat) (ps : IRList Nat) (vs : IRList IRScalar) : IRConfig := ",
                "IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(IRList.cons IRFrame ",
                "(ir_frame_goto f tgt (ir_bind_params ps vs (ir_frame_locals f))) rest) ",
                "mem na)) ",
                "fs) s",
            ),
            "Transfer control within a function, binding the target block's parameters to the \
             branch arguments on top of the existing locals. Keeping the old locals cannot shadow \
             anything: SSA ids are unique within a function, and a re-entered block rebinds its \
             own parameters to the new arguments, which the head-first lookup then finds.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_jump_block (s : IRMachine) (tgt : Nat) (vs : IRList IRScalar) (ob : IROption IRBlock) : IRConfig := ",
                "IROption.rec IRBlock (fun (_ : IROption IRBlock) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_block)) ",
                "(fun (b : IRBlock) => ir_goto s tgt (ir_block_params b) vs) ob",
            ),
            "Jump to a resolved block.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_jump_func (s : IRMachine) (tgt : Nat) (vs : IRList IRScalar) (of : IROption IRFunc) : IRConfig := ",
                "IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_func)) ",
                "(fun (f : IRFunc) => ir_jump_block s tgt vs (ir_block_find (ir_func_blocks f) tgt)) of",
            ),
            "Jump within a resolved function.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_cur_func (m : IRModule) (s : IRMachine) : IROption IRFunc := ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IROption IRFunc) ",
                "(IROption.none IRFunc) ",
                "(fun (f : IRFrame) (_ : IRList IRFrame) (_ : IROption IRFunc) => ",
                "ir_func_find (ir_mod_funcs m) (ir_frame_func f)) (ir_mach_frames s)",
            ),
            "The function the current frame is executing.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_jump (m : IRModule) (s : IRMachine) (tgt : Nat) (args : IRList Nat) : IRConfig := ",
                "ir_jump_func s tgt (ir_resolve s args) (ir_cur_func m s)",
            ),
            "Br, and the shared target of CondBr and Switch.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_condbr_b (m : IRModule) (s : IRMachine) (tt : Nat) (targs : IRList Nat) ",
                "(et : Nat) (eargs : IRList Nat) (b : Bool) : IRConfig := ",
                "Bool.rec (fun (_ : Bool) => IRConfig) ",
                "(ir_jump m s et eargs) (ir_jump m s tt targs) b",
            ),
            "CondBr on a decided condition. Bool.rec minor order is (false, true), so the first \
             minor is the else edge.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_condbr_exec (m : IRModule) (s : IRMachine) (c : IRScalar) (tt : Nat) ",
                "(targs : IRList Nat) (et : Nat) (eargs : IRList Nat) : IRConfig := ",
                "IROption.rec Bool (fun (_ : IROption Bool) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (b : Bool) => ir_condbr_b m s tt targs et eargs b) (ir_as_bool c)",
            ),
            "CondBr.",
        )?;

        self.add_recursive_def(
            r"def ir_case_target (c : IRSwitchCase) : Nat := match c with
| IRSwitchCase.mk v t a => t",
            "The target block of a Switch arm.",
        )?;
        self.add_recursive_def(
            r"def ir_case_args (c : IRSwitchCase) : IRList Nat := match c with
| IRSwitchCase.mk v t a => a",
            "The block arguments of a Switch arm.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_switch_n (m : IRModule) (s : IRMachine) (dflt : Nat) (dargs : IRList Nat) ",
                "(cases : IRList IRSwitchCase) (n : Nat) : IRConfig := ",
                "IROption.rec IRSwitchCase (fun (_ : IROption IRSwitchCase) => IRConfig) ",
                "(ir_jump m s dflt dargs) ",
                "(fun (c : IRSwitchCase) => ir_jump m s (ir_case_target c) (ir_case_args c)) ",
                "(ir_case_find cases n)",
            ),
            "Switch on a decided selector: the matching arm, else the default. The \
             exhaustive_enum_unreachable flag is carried on the instruction but licenses NOTHING \
             here — it claims the default arm is unreachable, which is a property to be PROVED \
             against this semantics, not an assumption the semantics may help itself to.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_switch_exec (m : IRModule) (s : IRMachine) (v : IRScalar) (dflt : Nat) ",
                "(dargs : IRList Nat) (cases : IRList IRSwitchCase) : IRConfig := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_int)) ",
                "(fun (n : Nat) => ir_switch_n m s dflt dargs cases n) (ir_as_int v)",
            ),
            "Switch.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_push (s : IRMachine) (rs : IRList Nat) (f : IRFunc) (vs : IRList IRScalar) : IRConfig := ",
                "IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (cur : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(IRList.cons IRFrame ",
                "(IRFrame.mk (ir_func_id f) (ir_func_entry f) Nat.zero ",
                "(ir_bind_params (ir_func_params f) vs (IRList.nil IRBinding)) rs) ",
                "(IRList.cons IRFrame (ir_frame_advance cur) rest)) ",
                "mem na)) ",
                "fs) s",
            ),
            "Push a callee frame. Three things happen at once and all three matter: the callee's \
             locals start EMPTY (SSA scoping), the caller's program counter is advanced NOW so the \
             return resumes after the call, and the call node's declared result ids travel with \
             the callee as its return destinations.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_call_exec (m : IRModule) (s : IRMachine) (rs : IRList Nat) (fid : Nat) (args : IRList Nat) : IRConfig := ",
                "IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_func)) ",
                "(fun (f : IRFunc) => ir_push s rs f (ir_resolve s args)) ",
                "(ir_func_find (ir_mod_funcs m) fid)",
            ),
            "Call. An unresolved callee is STUCK, not UB: a module whose reachable closure \
             contains a bodyless declaration is exactly what the crate-seam differential declines, \
             and this semantics declines it too rather than inventing a result.",
        )?;

        self.add_recursive_def(
            r"def ir_callind_exec (m : IRModule) (s : IRMachine) (rs : IRList Nat) (cv : IRScalar) (args : IRList Nat) : IRConfig := match cv with
| IRScalar.undef_ => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.bool_ b => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.int_ n => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.float_ n => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.unit_ => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.ptr_ a => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.nullptr_ => IRConfig.halted (IROutcome.ub IRFault.null_deref)
| IRScalar.fat_ d md => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.fnptr_ f => ir_call_exec m s rs f args
| IRScalar.aggv sp => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.vnil => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)
| IRScalar.vcons x rest => IRConfig.halted (IROutcome.type_error IRFault.not_fnptr)",
            "CallIndirect: resolve the callee value to a function id, then call. Calling through a \
             null function pointer is UB. The declared signature and calling convention are \
             carried on the instruction but not dispatched on — they are producer-side \
             well-formedness that validate_module cross-checks wherever the pointer's provenance \
             is statically visible.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_ret_to (dests : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) ",
                "(na : Nat) (vs : IRList IRScalar) : IRConfig := ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.ret vs)) ",
                "(fun (caller : IRFrame) (rest2 : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(IRList.cons IRFrame (ir_frame_set_many caller dests vs) rest2) mem na)) ",
                "rest",
            ),
            "Pop to the caller, binding the returned values positionally to the call node's \
             declared result ids — so a multi-value return needs no packing and loses nothing. \
             When the outermost frame returns, halt with the returned values.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_ret_vals (s : IRMachine) (vs : IRList IRScalar) : IRConfig := ",
                "IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (cur : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "ir_ret_to (ir_frame_dests cur) rest mem na vs) ",
                "fs) s",
            ),
            "Return with already-resolved values.",
        )?;

        self.add_recursive_def(
            "def ir_return_exec (s : IRMachine) (ids : IRList Nat) : IRConfig := ir_ret_vals s (ir_resolve s ids)",
            "Return.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_assert_b (s : IRMachine) (b : Bool) : IRConfig := ",
                "Bool.rec (fun (_ : Bool) => IRConfig) ",
                "(IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_advance s) b",
            ),
            "Assert on a decided condition: a false assertion is UB, which is how a Rust panic \
             path shows up in this model.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_assert_exec (s : IRMachine) (c : IRScalar) : IRConfig := ",
                "IROption.rec Bool (fun (_ : IROption Bool) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (b : Bool) => ir_assert_b s b) (ir_as_bool c)",
            ),
            "Assert.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_select_eval (c : IRScalar) (a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (x : Bool) => Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.value b) (IRStepResult.value a) x) (ir_as_bool c)",
            ),
            "Select: the branch-free conditional. Bool.rec minor order is (false, true).",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_globaladdr_eval (m : IRModule) (g : Nat) : IRStepResult := ",
                "IROption.rec IRGlobal (fun (_ : IROption IRGlobal) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.no_global)) ",
                "(fun (_ : IRGlobal) => IRStepResult.value (IRScalar.ptr_ g)) ",
                "(ir_global_find (ir_mod_globals m) g)",
            ),
            "GlobalAddr. A global's id IS its address: ir_init materializes one cell per global at \
             that address, so repeated address-of aliases — the property the Lean model needs its \
             globals cache for.",
        )?;

        Ok(())
    }

    /// The 28-arm dispatch, the fetch step, and the fuel-driven driver.
    fn add_eval_ir_dispatch(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def ir_exec (m : IRModule) (i : IRInst) (rs : IRList Nat) (s : IRMachine) : IRConfig := match i with
| IRInst.binop op t a b => ir_bind_result s rs (ir_binop_eval op t (ir_getd s a) (ir_getd s b))
| IRInst.unop op t a => ir_bind_result s rs (ir_unop_eval op t (ir_getd s a))
| IRInst.overflow op t a b => IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)
| IRInst.icmp op t a b => ir_bind_result s rs (ir_icmp_eval op t (ir_getd s a) (ir_getd s b))
| IRInst.fcmp op t a b => ir_bind_result s rs (ir_fcmp_eval op (ir_getd s a) (ir_getd s b))
| IRInst.cast op sr ds a => ir_bind_result s rs (ir_cast_eval op sr ds (ir_getd s a))
| IRInst.load t p vol => ir_bind_result s rs (ir_load_eval s (ir_getd s p))
| IRInst.store t p v vol => ir_store_exec s (ir_getd s p) (ir_getd s v)
| IRInst.alloca t c => ir_alloca_exec s rs c
| IRInst.gep t b idxs inb => ir_bind_result s rs (ir_gep_eval (ir_getd s b) (ir_resolve s idxs))
| IRInst.ptrdata t p => ir_bind_result s rs (ir_ptrdata_eval (ir_getd s p))
| IRInst.ptrmetadata pt mt p => ir_bind_result s rs (ir_ptrmeta_eval (ir_getd s p))
| IRInst.ptrfromparts pt mt d md => ir_bind_result s rs (ir_ptrparts_eval (ir_getd s d) (ir_getd s md))
| IRInst.br tgt args => ir_jump m s tgt args
| IRInst.condbr c tt targs et eargs => ir_condbr_exec m s (ir_getd s c) tt targs et eargs
| IRInst.switch v dflt dargs cases exh => ir_switch_exec m s (ir_getd s v) dflt dargs cases
| IRInst.call fid args => ir_call_exec m s rs fid args
| IRInst.callindirect cid sig args cc => ir_callind_exec m s rs (ir_getd s cid) args
| IRInst.ret ids => ir_return_exec s ids
| IRInst.extractfield t a k => ir_bind_result s rs (ir_ef_at (ir_getd s a) k)
| IRInst.insertfield t a k v => ir_bind_result s rs (ir_insert_field (ir_getd s a) k (ir_getd s v))
| IRInst.extractelement t a k => ir_bind_result s rs (ir_extract_elem (ir_getd s a) (ir_getd s k))
| IRInst.const_ t c => ir_bind_result s rs (ir_const_eval t c)
| IRInst.globaladdr g => ir_bind_result s rs (ir_globaladdr_eval m g)
| IRInst.undef t => ir_bind s rs IRScalar.undef_
| IRInst.assert c => ir_assert_exec s (ir_getd s c)
| IRInst.unreachable => IRConfig.halted (IROutcome.ub IRFault.unreachable)
| IRInst.select t c a b => ir_bind_result s rs (ir_select_eval (ir_getd s c) (ir_getd s a) (ir_getd s b))",
            "THE COVERAGE CLAIM: 28 arms, one per constructed trust_ir::Inst variant. Exactly two \
             arms are the tagged unmodelled outcome by design (overflow needs a width-bounded \
             value domain; fcmp needs a float domain) — every other arm is real semantics. No arm \
             is a catch-all and none is missing, so the fraction is checkable constructor by \
             constructor.",
        )?;

        // ===================================================================
        // THE THREE OPERANDS THE DISPATCH DROPS, PROVED INERT.
        //
        // `ir_exec` above drops exactly three operands of the instructions it
        // executes: `Switch.exhaustive_enum_unreachable`, and
        // `CallIndirect`'s signature index and calling convention. Each was
        // documented as dropped IN A COMMENT — `eval_ir_syntax.rs` says of the
        // convention that "nothing in the semantics dispatches on it; it is
        // retained so … an adequacy theorem has something to quantify over".
        //
        // These are that theorem. A comment is not a check, and this one is
        // load-bearing in a way the comment could not be: the exhaustive flag
        // is the slot trust-ir's `Display` NEVER PRINTS, so no reader of the
        // emitted text can witness it, and the hand transcription had it WRONG
        // (`Bool.true` against a measured `false` on three producer dumps and
        // four sibling chains). What makes that a lineage defect rather than a
        // soundness defect is precisely that the machine cannot see the flag —
        // and that is now kernel-checked at EVERY module, state, selector,
        // default, argument list and case list rather than argued.
        //
        // Same standard as `ir_ty_is_agg_enum_any`, and the same mechanism: the
        // kernel iota-reduces the match on the constructor, so the dropped
        // field never appears in the answer and `Eq.refl` closes it.
        // ===================================================================
        self.add_recursive_def(
            concat!(
                "def ir_exec_switch_exh_irrelevant (m : IRModule) (v : Nat) (dflt : Nat) ",
                "(dargs : IRList Nat) (cases : IRList IRSwitchCase) (rs : IRList Nat) ",
                "(s : IRMachine) : Eq IRConfig ",
                "(ir_exec m (IRInst.switch v dflt dargs cases Bool.true) rs s) ",
                "(ir_exec m (IRInst.switch v dflt dargs cases Bool.false) rs s) := ",
                "Eq.refl IRConfig (ir_switch_exec m s (ir_getd s v) dflt dargs cases)",
            ),
            "ir_exec_switch_exh_irrelevant: the machine's step on a `switch` is THE SAME \
             CONFIGURATION whichever way `exhaustive_enum_unreachable` is set — at every module, \
             state, selector, default, argument list and case list. This is the field trust-ir's \
             Display never prints, so no text-anchored reader can witness it; the flag's value is \
             therefore a LINEAGE fact about which module was emitted and provably not a fact \
             about what that module computes. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_exec_callind_conv_irrelevant (m : IRModule) (cid : Nat) (sig : Nat) ",
                "(args : IRList Nat) (cc1 : Nat) (cc2 : Nat) (rs : IRList Nat) (s : IRMachine) : ",
                "Eq IRConfig (ir_exec m (IRInst.callindirect cid sig args cc1) rs s) ",
                "(ir_exec m (IRInst.callindirect cid sig args cc2) rs s) := ",
                "Eq.refl IRConfig (ir_callind_exec m s rs (ir_getd s cid) args)",
            ),
            "ir_exec_callind_conv_irrelevant: the CALLING CONVENTION operand cannot change the \
             step, at any two conventions. `eval_ir_syntax.rs` keeps the field so \"an adequacy \
             theorem has something to quantify over\"; this is it. It is also the semantic half \
             of the `cc-and-linkage` blind slot — the convention is outside the fragment because \
             the fragment provably does not consult it. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_exec_callind_sig_irrelevant (m : IRModule) (cid : Nat) (g1 : Nat) ",
                "(g2 : Nat) (args : IRList Nat) (cc : Nat) (rs : IRList Nat) (s : IRMachine) : ",
                "Eq IRConfig (ir_exec m (IRInst.callindirect cid g1 args cc) rs s) ",
                "(ir_exec m (IRInst.callindirect cid g2 args cc) rs s) := ",
                "Eq.refl IRConfig (ir_callind_exec m s rs (ir_getd s cid) args)",
            ),
            "ir_exec_callind_sig_irrelevant: the SIGNATURE-TABLE index cannot change the step \
             either. That index is the same whole-crate `functy.N` the header carries and the \
             `functy-index` blind slot names — measured to renumber on every producer change with \
             no instruction changed — so this is the kernel-checked reason the core module may \
             drop it. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            r"def ir_exec_node (m : IRModule) (n : IRNode) (s : IRMachine) : IRConfig := match n with
| IRNode.mk i rs => ir_exec m i rs s",
            "Execute a node: its instruction, with its declared result ids.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_step_n (m : IRModule) (s : IRMachine) (on : IROption IRNode) : IRConfig := ",
                "IROption.rec IRNode (fun (_ : IROption IRNode) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.fetch_past_end)) ",
                "(fun (n : IRNode) => ir_exec_node m n s) on",
            ),
            "Execute a fetched node. Running off the end of a block is STUCK: a block without a \
             terminator does not fall through into its successor.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_step_b (m : IRModule) (s : IRMachine) (pc : Nat) (ob : IROption IRBlock) : IRConfig := ",
                "IROption.rec IRBlock (fun (_ : IROption IRBlock) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_block)) ",
                "(fun (b : IRBlock) => ir_step_n m s (ir_nodes_get (ir_block_nodes b) pc)) ob",
            ),
            "Fetch within a resolved block.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_step_f (m : IRModule) (s : IRMachine) (bl : Nat) (pc : Nat) (of : IROption IRFunc) : IRConfig := ",
                "IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_func)) ",
                "(fun (f : IRFunc) => ir_step_b m s pc (ir_block_find (ir_func_blocks f) bl)) of",
            ),
            "Fetch within a resolved function.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_step_frame (m : IRModule) (s : IRMachine) (f : IRFrame) : IRConfig := ",
                "ir_step_f m s (ir_frame_block f) (ir_frame_pc f) ",
                "(ir_func_find (ir_mod_funcs m) (ir_frame_func f))",
            ),
            "Fetch and execute one node for a frame.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_step (m : IRModule) (s : IRMachine) : IRConfig := ",
                "IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (_ : IRList IRFrame) (_ : IRConfig) => ir_step_frame m s f) ",
                "(ir_mach_frames s)",
            ),
            "One machine step.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_run (fuel : Nat) (m : IRModule) (c : IRConfig) : IROutcome := ",
                "Nat.rec (fun (_ : Nat) => IRConfig -> IROutcome) ",
                "(fun (c0 : IRConfig) => IRConfig.rec (fun (_ : IRConfig) => IROutcome) ",
                "(fun (_ : IRMachine) => IROutcome.fuel_out) (fun (o : IROutcome) => o) c0) ",
                "(fun (_ : Nat) (ih : IRConfig -> IROutcome) => fun (c0 : IRConfig) => ",
                "IRConfig.rec (fun (_ : IRConfig) => IROutcome) ",
                "(fun (s : IRMachine) => ih (ir_step m s)) (fun (o : IROutcome) => o) c0) ",
                "fuel c",
            ),
            "Run to a halt or until the fuel runs out. Exhaustion is its OWN outcome, distinct \
             from every real result, so no theorem can mistake it for success.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_globals_mem (gs : IRList IRGlobal) : IRList IRMemSlot := ",
                "IRList.rec IRGlobal (fun (_ : IRList IRGlobal) => IRList IRMemSlot) ",
                "(IRList.nil IRMemSlot) ",
                "(fun (g : IRGlobal) (_ : IRList IRGlobal) (ih : IRList IRMemSlot) => ",
                "IRGlobal.rec (fun (_ : IRGlobal) => IRList IRMemSlot) ",
                "(fun (i : Nat) (c : IRConst) => ",
                "IRList.cons IRMemSlot (IRMemSlot.mk i (ir_const_value c) Bool.true) ih) g) gs",
            ),
            "Materialize one live cell per global, at the address that is its id.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_mem_concat (a : IRList IRMemSlot) (b : IRList IRMemSlot) : IRList IRMemSlot := ",
                "IRList.rec IRMemSlot (fun (_ : IRList IRMemSlot) => IRList IRMemSlot) b ",
                "(fun (x : IRMemSlot) (_ : IRList IRMemSlot) (ih : IRList IRMemSlot) => ",
                "IRList.cons IRMemSlot x ih) a",
            ),
            "Append two memories, globals first.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_init (m : IRModule) (fid : Nat) (args : IRList IRScalar) ",
                "(mem0 : IRList IRMemSlot) (na : Nat) : IRConfig := ",
                "IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_func)) ",
                "(fun (f : IRFunc) => IRConfig.running (IRMachine.mk ",
                "(IRList.cons IRFrame (IRFrame.mk (ir_func_id f) (ir_func_entry f) Nat.zero ",
                "(ir_bind_params (ir_func_params f) args (IRList.nil IRBinding)) (IRList.nil Nat)) ",
                "(IRList.nil IRFrame)) ",
                "(ir_mem_concat (ir_globals_mem (ir_mod_globals m)) mem0) na)) ",
                "(ir_func_find (ir_mod_funcs m) fid)",
            ),
            "Build the initial configuration. mem0 is the CALLER-SUPPLIED heap: this is the hook a \
             representation premise constrains (Phase-A job A2's EncodesLiveLevelRef / \
             EncodesLevelArc) rather than an unconstrained existential. It is the ONLY such hook: \
             aggregates are inline values, so there is no second store to constrain jointly with \
             it and no closure side condition relating the two. The outermost frame has no return \
             destinations, so its Return halts the machine.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_eval (fuel : Nat) (m : IRModule) (fid : Nat) (args : IRList IRScalar) ",
                "(mem0 : IRList IRMemSlot) (na : Nat) : IROutcome := ",
                "ir_run fuel m (ir_init m fid args mem0 na)",
            ),
            "THE ENTRY POINT. `ir_eval fuel M f args heap na = IROutcome.ret [v]` is the shape of \
             the crystal's equality theorem, with the heap pinned by a representation relation and \
             M pinned by an artifact digest.",
        )?;

        Ok(())
    }
}
