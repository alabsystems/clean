// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — machine transitions, the exhaustive dispatch, and the driver (**C3**).
//!
//! `ir_exec` has one arm per shared `IRInst` constructor. Thirty execute their
//! declared legacy fragments; the appended sequential byte fetch-add explicitly
//! halts as unmodelled because this cell machine lacks its byte-memory semantics.
//! Exhaustive syntax is not successful atomic execution coverage. `ir_step` fetches a node; `ir_run`
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
        self.add_eval_ir_overflow()?;
        self.add_eval_ir_dispatch()?;
        // W5 (2026-08-25): the adequacy grid's theorem band — the sixteen
        // remaining dropped-operand irrelevance theorems, appended LAST so
        // every pre-existing def keeps its registration position (the W4
        // precedent). See `eval_ir_adequacy.rs` and
        // `data/evalir_adequacy_grid.json`.
        self.add_eval_ir_adequacy()
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
| IRModule.mk fs gs => fs
| IRModule.mkv fs gs es => fs",
            "The functions of a module, in either module form.",
        )?;
        self.add_recursive_def(
            r"def ir_mod_globals (m : IRModule) : IRList IRGlobal := match m with
| IRModule.mk fs gs => gs
| IRModule.mkv fs gs es => gs",
            "The globals of a module, in either module form.",
        )?;
        self.add_recursive_def(
            r"def ir_mod_encs (m : IRModule) : IRList IREnc := match m with
| IRModule.mk fs gs => @IRList.nil IREnc
| IRModule.mkv fs gs es => es",
            "The DERIVED encodings table of a module. A pre-Phase-B `IRModule.mk` has none, and \
             that arm is the whole conservativity argument: `ir_load_view (ir_mod_encs \
             (IRModule.mk fs gs)) t r` iota-reduces to `r` at an abstract module, type and \
             result, so the encoding-aware load is definitionally the old load on every module \
             minted before this stage existed.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_opt_value (o : IROption IRScalar) : IRScalar := ",
                "@IROption.rec IRScalar (fun (_ : IROption IRScalar) => IRScalar) ",
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
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRScalar) IRScalar.undef_ ",
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
                "@IRList.rec Nat (fun (_ : IRList Nat) => IRList IRScalar) (@IRList.nil IRScalar) ",
                "(fun (i : Nat) (_ : IRList Nat) (ih : IRList IRScalar) => ",
                "@IRList.cons IRScalar (ir_getd s i) ih) ids",
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
                "@IRList.rec Nat (fun (_ : IRList Nat) => IRList IRScalar -> IRList IRBinding) ",
                "(fun (_ : IRList IRScalar) => loc) ",
                "(fun (p : Nat) (_ : IRList Nat) (ih : IRList IRScalar -> IRList IRBinding) => ",
                "fun (ws : IRList IRScalar) => ",
                "@IRList.rec IRScalar (fun (_ : IRList IRScalar) => IRList IRBinding) ",
                "loc ",
                "(fun (w : IRScalar) (wrest : IRList IRScalar) (_ : IRList IRBinding) => ",
                "@IRList.cons IRBinding (IRBinding.mk p w) (ih wrest)) ",
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
| IRFrame.mk fnid bl pc loc ds => IRFrame.mk fnid bl (Nat.succ pc) (ir_bind_params rs (@IRList.cons IRScalar v (@IRList.nil IRScalar)) loc) ds",
            "Bind a value-producing instruction's single result to the FIRST id the node declares, \
             and advance past it. A node with an empty result list evaluates the instruction and \
             discards the value, which is what an unused result means.",
        )?;

        self.add_recursive_def(
            r"def ir_frame_bind2 (f : IRFrame) (rs : IRList Nat) (v : IRScalar) (u : IRScalar) : IRFrame := match f with
| IRFrame.mk fnid bl pc loc ds => IRFrame.mk fnid bl (Nat.succ pc) (ir_bind_params rs (@IRList.cons IRScalar v (@IRList.cons IRScalar u (@IRList.nil IRScalar))) loc) ds",
            "Bind a TWO-result instruction's values positionally to the ids the node declares, \
             and advance past it — the same ir_bind_params multi-bind the return path uses \
             (ir_frame_set_many), plus the advance an instruction needs and a return does not. \
             Added 2026-08-25 (plan W3) for Overflow, whose trust-ir node declares two results \
             (a value and a flag) bound positionally (a4e81b6 interpret.rs:637-644). The \
             length-mismatch posture is ir_bind_params's own: a node declaring fewer ids binds \
             the prefix — arity is producer-side well-formedness — where the reference \
             interpreter's bind_results rejects the mismatch as malformed_instruction \
             (interpret.rs:5339-5361); on producer modules the arities agree and the split is \
             junk-module-only, recorded here rather than smoothed.",
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
                "@IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(@IRList.cons IRFrame (ir_frame_bind f rs v) rest) mem na)) ",
                "fs) s",
            ),
            "Bind a result at the ids the current node declares, and advance.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_bind_result (s : IRMachine) (rs : IRList Nat) (r : IRStepResult) : IRConfig := ",
                "@IRStepResult.rec (fun (_ : IRStepResult) => IRConfig) ",
                "(fun (v : IRScalar) => ir_bind s rs v) ",
                "(fun (o : IROutcome) => IRConfig.halted o) r",
            ),
            "Bind a value-level evaluator's result, or halt on its fault.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_bind2 (s : IRMachine) (rs : IRList Nat) (v : IRScalar) (u : IRScalar) : IRConfig := ",
                "@IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(@IRList.cons IRFrame (ir_frame_bind2 f rs v u) rest) mem na)) ",
                "fs) s",
            ),
            "Bind a two-result instruction's pair at the ids the current node declares, and \
             advance — ir_bind's shape with ir_frame_bind2 in place of ir_frame_bind.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_advance (s : IRMachine) : IRConfig := ",
                "@IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(@IRList.cons IRFrame (ir_frame_advance f) rest) mem na)) ",
                "fs) s",
            ),
            "Advance past a value-less instruction.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_set_mem (s : IRMachine) (m2 : IRList IRMemSlot) : IRMachine := ",
                "@IRMachine.rec (fun (_ : IRMachine) => IRMachine) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "IRMachine.mk fs m2 na) s",
            ),
            "Replace the memory.",
        )?;

        Ok(())
    }

    /// Load, Store, Alloca, GEP and the pointer-lane instructions.
    fn add_eval_ir_memory(&mut self) -> Result<(), SpecError> {
        // ===================================================================
        // THE ENCODING-AWARE LOAD VIEW (Phase B, link 3).
        //
        // A cell-addressed load returns the value the cell HOLDS. The
        // reference decodes the cell's BYTE IMAGE at the load's type, and for
        // a niche-encoded enum over a pointer payload that decode is not the
        // identity: the word 0 is the `none` variant and any other word is the
        // `some` variant carrying the payload (`decode_value`'s niche arm).
        // These definitions are that decode, and only that decode.
        //
        // Three properties are load-bearing, and each is checked by a
        // registered witness rather than argued here:
        //
        //  1. CONSERVATIVE. `ir_enc_find` on the EMPTY table is `none`, so
        //     `ir_load_view (ir_mod_encs (IRModule.mk fs gs)) t r` reduces to
        //     `r` — an `Eq.refl` at abstract fs/gs/t/r. Every module minted
        //     before this stage is an `IRModule.mk`.
        //  2. PARTIAL, DELIBERATELY. A load type with no row keeps today's
        //     semantics. That is what (1) rests on, and it is also why the
        //     view is NOT a whole-module faithfulness claim: an enum whose
        //     descriptor fails an F9 clause is deliberately left out, and the
        //     load still runs on the model's own tag encoding.
        //  3. SHAPE-TOLERANT. `ir_view_word` decodes only the WORD-shaped
        //     scalars (`ptr_`, `nullptr_`, `int_`) and is the identity on
        //     every other one. The chain needs this: `as_deref` stores an
        //     inline aggregate into an `alloca enum.0` and loads it back at
        //     the same type a heap word is loaded at elsewhere, so the view
        //     must pass an `aggv` through unchanged. The reference always
        //     decodes the byte image it wrote, so the two agree exactly when
        //     the model's store/load round-trip and the reference's
        //     encode/decode round-trip agree — recorded as the declared delta
        //     `enum-load-shape-directed`.
        // ===================================================================
        self.add_recursive_def(
            concat!(
                "def ir_enc_len (l : IRList IREnc) : Nat := ",
                "@IRList.rec IREnc (fun (_ : IRList IREnc) => Nat) Nat.zero ",
                "(fun (_ : IREnc) (_ : IRList IREnc) (ih : Nat) => Nat.succ ih) l",
            ),
            "The number of rows in an encodings table. It is also the view's FUEL: a row's \
             payload type may itself have a row (enum -> Arc struct -> NonNull struct -> ptr is \
             depth three on the crystal chain), and a table cannot chain deeper than it is long \
             without repeating a row, so the row count bounds the nesting.",
        )?;

        self.add_recursive_def(
            r"def ir_enc_matches (e : IREnc) (t : IRTy) : Bool := match t with
| IRTy.enum_ j => @IREnc.rec (fun (_ : IREnc) => Bool) (fun (k : Nat) (no : Nat) (so : Nat) (p : IRTy) => ir_nat_eqb k j) (fun (k : Nat) (i : Nat) (c : Nat) (p : IRTy) => Bool.false) e
| IRTy.struct_ j => @IREnc.rec (fun (_ : IREnc) => Bool) (fun (k : Nat) (no : Nat) (so : Nat) (p : IRTy) => Bool.false) (fun (k : Nat) (i : Nat) (c : Nat) (p : IRTy) => ir_nat_eqb k j) e
| _ => Bool.false",
            "Does this row describe this type? The key is (KIND, id), never the id alone: the \
             crystal's own table carries an `enum 0` and a `struct 0` row, so an id-only key \
             would silently pick one of them for both. A nicheptr row answers only at \
             `IRTy.enum_`, a ptrwrap row only at `IRTy.struct_`; every other type is unencoded \
             and keeps the identity load.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_enc_find (l : IRList IREnc) (t : IRTy) : IROption IREnc := ",
                "@IRList.rec IREnc (fun (_ : IRList IREnc) => IROption IREnc) ",
                "(@IROption.none IREnc) ",
                "(fun (e : IREnc) (_ : IRList IREnc) (ih : IROption IREnc) => ",
                "@Bool.rec (fun (_ : Bool) => IROption IREnc) ih (@IROption.some IREnc e) ",
                "(ir_enc_matches e t)) l",
            ),
            "The FIRST row matching a type, or none. First-match is why the table's derivation \
             refuses two rows whose canonical matched IRTy coincides: with two, this would \
             silently pick one. An absent row is `none`, and every consumer reads that as the \
             identity — fail-OPEN here is what conservativity means, and it is the reason a \
             derived row that fails any F9 clause is simply not minted.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_zst_spine (n : Nat) : IRScalar := ",
                "@Nat.rec (fun (_ : Nat) => IRScalar) IRScalar.vnil ",
                "(fun (_ : Nat) (ih : IRScalar) => ",
                "IRScalar.vcons (IRScalar.aggv IRScalar.vnil) ih) n",
            ),
            "A spine of n zero-sized fields. `aggv vnil` is the model's image of a ZST: it is \
             what the reference's decode_value returns for a zero-FIELD aggregate, which is why \
             the derivation rule refuses any other spelling of a ZST slot (Ty::Unit, a Tuple, a \
             zero-length Array) rather than mapping it here.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_spine_with_slot (i : Nat) (c : Nat) (v : IRScalar) : IRScalar := ",
                "@Nat.rec (fun (_ : Nat) => IRScalar) ",
                "(IRScalar.vcons v (ir_zst_spine (Nat.sub c (Nat.succ i)))) ",
                "(fun (_ : Nat) (ih : IRScalar) => ",
                "IRScalar.vcons (IRScalar.aggv IRScalar.vnil) ih) i",
            ),
            "The c-field spine whose slot i is v and whose other slots are ZSTs. The base case \
             is stated at the OUTER i, so the recursion prepends i ZSTs to `v :: (c - i - 1) \
             ZSTs` and the length is c at every i < c. A row with i >= c cannot be derived (the \
             derivation checks `fields[i]` exists), and if one were, `Nat.sub` truncates and the \
             spine is short rather than ill-formed.",
        )?;

        self.add_recursive_def(
            r"def ir_niche_image (payload : IRScalar) (no : Nat) (so : Nat) (v : IRScalar) : IRScalar := match v with
| IRScalar.undef_ => IRScalar.undef_
| IRScalar.bool_ b => IRScalar.bool_ b
| IRScalar.int_ n => @Nat.rec (fun (_ : Nat) => IRScalar) (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ no) IRScalar.vnil)) (fun (_ : Nat) (_ : IRScalar) => IRScalar.aggv (IRScalar.vcons (IRScalar.int_ so) (IRScalar.vcons payload IRScalar.vnil))) n
| IRScalar.float_ n => IRScalar.float_ n
| IRScalar.unit_ => IRScalar.unit_
| IRScalar.ptr_ a => @Nat.rec (fun (_ : Nat) => IRScalar) (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ no) IRScalar.vnil)) (fun (_ : Nat) (_ : IRScalar) => IRScalar.aggv (IRScalar.vcons (IRScalar.int_ so) (IRScalar.vcons payload IRScalar.vnil))) a
| IRScalar.nullptr_ => IRScalar.aggv (IRScalar.vcons (IRScalar.int_ no) IRScalar.vnil)
| IRScalar.fat_ d md => IRScalar.fat_ d md
| IRScalar.fnptr_ f => IRScalar.fnptr_ f
| IRScalar.aggv sp => IRScalar.aggv sp
| IRScalar.vnil => IRScalar.vnil
| IRScalar.vcons x rest => IRScalar.vcons x rest",
            "THE WORD-0 CLAUSE. A niche-encoded two-variant enum over a pointer payload stores \
             the payload word directly: word 0 is the `no` variant with no fields, any other \
             word is the `so` variant carrying the payload. That is the reference's decode at \
             `niche_start = 0` over an empty variant range, and the derivation refuses a row \
             whose descriptor says anything else, because the model cannot read those fields to \
             compute the polarity itself. BOTH of Clean's spellings of the zero word — \
             `nullptr_` and `ptr_ Nat.zero` — take the none image. The tag-at-slot-0 shape is \
             `ir_var`'s, so ExtractField reads the result with no special case. Every non-word \
             scalar is the IDENTITY: a cell holding an inline aggregate is passed through, which \
             is what an alloca'd enum round-tripped through store/load is.",
        )?;

        self.add_recursive_def(
            r"def ir_wrap_image (payload : IRScalar) (i : Nat) (c : Nat) (v : IRScalar) : IRScalar := match v with
| IRScalar.undef_ => IRScalar.undef_
| IRScalar.bool_ b => IRScalar.bool_ b
| IRScalar.int_ n => IRScalar.aggv (ir_spine_with_slot i c payload)
| IRScalar.float_ n => IRScalar.float_ n
| IRScalar.unit_ => IRScalar.unit_
| IRScalar.ptr_ a => IRScalar.aggv (ir_spine_with_slot i c payload)
| IRScalar.nullptr_ => IRScalar.aggv (ir_spine_with_slot i c payload)
| IRScalar.fat_ d md => IRScalar.fat_ d md
| IRScalar.fnptr_ f => IRScalar.fnptr_ f
| IRScalar.aggv sp => IRScalar.aggv sp
| IRScalar.vnil => IRScalar.vnil
| IRScalar.vcons x rest => IRScalar.vcons x rest",
            "A pointer-wrapper struct's image: the whole word IS the payload, at field i, with \
             ZSTs elsewhere. No niche arithmetic — a wrapper has one variant. Same shape \
             tolerance as ir_niche_image: only a word-shaped scalar is decoded.",
        )?;

        self.add_recursive_def(
            r"def ir_view_word (rec_ : IRTy → IRScalar → IRScalar) (e : IREnc) (v : IRScalar) : IRScalar := match e with
| IREnc.nicheptr k no so p => ir_niche_image (rec_ p v) no so v
| IREnc.ptrwrap k i c p => ir_wrap_image (rec_ p v) i c v",
            "Image one word at one row. `rec_` is the view at the payload type, applied to the \
             SAME word: a niche-encoded Option<Arc<Level>> stores the Arc's pointer word, so the \
             Some payload is that word imaged at the Arc's own row. Eager application is \
             harmless — the none arms discard it.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_view_ty (encs : IRList IREnc) (n : Nat) : IRTy → IRScalar → IRScalar := ",
                "@Nat.rec (fun (_ : Nat) => IRTy → IRScalar → IRScalar) ",
                "(fun (t : IRTy) (v : IRScalar) => v) ",
                "(fun (k : Nat) (ih : IRTy → IRScalar → IRScalar) (t : IRTy) (v : IRScalar) => ",
                "@IROption.rec IREnc (fun (_ : IROption IREnc) => IRScalar) v ",
                "(fun (e : IREnc) => ir_view_word ih e v) (ir_enc_find encs t)) n",
            ),
            "The view at a type, with n rows of fuel. Out of fuel is the IDENTITY, not a fault: \
             running out means the table chains deeper than it is long, which the derivation \
             cannot mint, and failing OPEN there keeps the conservativity argument uniform. \
             Function-valued motive because the recursion is on the payload TYPE, not on a \
             structural argument — the level_eqb idiom.",
        )?;

        self.add_recursive_def(
            r"def ir_view_result (encs : IRList IREnc) (e : IREnc) (r : IRStepResult) : IRStepResult := match r with
| IRStepResult.value v => IRStepResult.value (ir_view_word (ir_view_ty encs (ir_enc_len encs)) e v)
| IRStepResult.fault o => IRStepResult.fault o",
            "Lift the word image over a step result: a fault is unchanged, a value is imaged. \
             The fuel handed to the payload view is the table's own length.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_load_view (encs : IRList IREnc) (t : IRTy) (r : IRStepResult) : IRStepResult := ",
                "@IROption.rec IREnc (fun (_ : IROption IREnc) => IRStepResult) ",
                "r (fun (e : IREnc) => ir_view_result encs e r) (ir_enc_find encs t)",
            ),
            "THE VIEW. It branches on the TABLE first and on the result second, and that order \
             is load-bearing: with an empty table the @IROption.rec iota-reduces to `r` without \
             ever matching `r`, so `ir_load_view (ir_mod_encs (IRModule.mk fs gs)) t r` is \
             `Eq.refl`-equal to `r` at an ABSTRACT r. A version that matched the result first \
             would be stuck at an abstract one and no conservativity witness could be written.",
        )?;

        // ===================================================================
        // BORROW — the reference's arm is a PROVENANCE check, not a no-op.
        //
        // `expect_pointer` (trust-ir interpret.rs) faults on three of the five
        // pointer kinds the reference can hold: NullPtr is UB "null pointer
        // dereference", DanglingPtr is UB "no allocation provenance", and a
        // partially-initialized value is UB via reject_partial. A FatPtr is
        // passed through VERBATIM with no check at all (the arm constructs
        // nothing and re-validates neither lane).
        //
        // The DanglingPtr arm is the one that matters here, and the reason it
        // needs modelling rather than a declared delta: the reference makes a
        // DanglingPtr in `decode_value`, on EVERY pointer word it reads out of
        // memory whose address names no allocation (`resolve_pointer_kind`),
        // and GEP propagates it. The crystal chain's own `Arc::deref` borrows
        // exactly such a word — loaded from the heap, then geped. So a model
        // whose borrow were the identity would CONTINUE where the reference
        // faults, which is the direction that turns a false theorem into a
        // proof. The model already has the analogue one cell away —
        // `ir_load_at` resolves `ptr_ a` through `ir_mem_lookup` and reads a
        // missing cell as `ub bad_addr` — so borrow uses it too.
        //
        // The residue, stated rather than hidden: the model's null is
        // `nullptr_`, and `ptr_ Nat.zero` is an ordinary address in its own
        // address space (an alloca at counter zero allocates there), whereas
        // the reference reads address 0 as NullPtr. That is the machine's
        // pre-existing address-space convention, shared verbatim with
        // `ir_load_at` and `ir_store_at`; borrow inherits it rather than
        // introducing it, and a zero test here would additionally make the arm
        // stuck at the ABSTRACT allocation counter every return-slot lemma is
        // stated over.
        //
        // The residue runs the OTHER way too, and that direction is declared
        // rather than left to be discovered. `try_pointer_from_address`
        // (interpret.rs:5396-5406, trust 0dd9d3e2d7) has a SECOND loop that
        // accepts `address == allocation.base + allocation.size`, so a
        // one-past-the-end address resolves to `Ptr` and `expect_pointer`
        // (interpret.rs:5648-5670) admits it. `ir_alloc_cells` materialises
        // cells only at `base .. base+k-1` and `ir_gep_eval` adds an unbounded
        // offset with no bound check, so the same borrow is `ub bad_addr`
        // here. That is FAIL-CLOSED — the model refuses where the reference
        // continues — and it is shared verbatim with `ir_load_at` and
        // `ir_store_at`, which resolve through the same `ir_mem_lookup`. Its
        // permanent home is the grid row `borrow-one-past-the-end`.
        // ===================================================================
        self.add_recursive_def(
            concat!(
                "def ir_borrow_slot (a : Nat) (o : IROption IRMemSlot) : IRStepResult := ",
                "@IROption.rec IRMemSlot (fun (_ : IROption IRMemSlot) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.bad_addr)) ",
                "(fun (c : IRMemSlot) => @IRMemSlot.rec ",
                "(fun (_ : IRMemSlot) => IRStepResult) ",
                "(fun (_ : Nat) (_ : IRScalar) (lv : Bool) => ",
                "@Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.bad_addr)) ",
                "(IRStepResult.value (IRScalar.ptr_ a)) lv) c) o",
            ),
            "The provenance half of Borrow: an address with no live cell has no allocation to \
             reach through, which is the reference's `DanglingPtr` arm of expect_pointer — UB, \
             not a value. A DEAD cell is refused for the same reason the reference refuses a \
             freed allocation: `try_pointer_from_address` finds no live allocation for it.",
        )?;

        self.add_recursive_def(
            r"def ir_borrow_eval (mem : IRList IRMemSlot) (v : IRScalar) : IRStepResult := match v with
| IRScalar.undef_ => IRStepResult.fault (IROutcome.ub IRFault.uninit)
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => ir_borrow_slot a (ir_mem_lookup mem a)
| IRScalar.nullptr_ => IRStepResult.fault (IROutcome.ub IRFault.null_deref)
| IRScalar.fat_ d md => IRStepResult.value (IRScalar.fat_ d md)
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "Borrow, arm for arm against the reference's expect_pointer: a live-cell pointer \
             passes through, a fat pointer passes through UNCHECKED (the reference's arm \
             re-validates neither lane), null is ub null_deref, poison is ub uninit via \
             reject_partial, and every non-pointer is a type_error. The provenance-free case is \
             ir_borrow_slot's none/dead minor.",
        )?;

        // ===================================================================
        // COPY — the type slot is READ, because the reference reads it.
        //
        // The reference's arm is `expect_ty(operand, ty)?` followed by a
        // rebind of the same value, and expect_ty is a dynamic type EQUALITY
        // whose failure is a `type_error`. So `copy.ty` decides
        // accept-versus-fault, and an irrelevance theorem for it would be an
        // adequacy claim the reference refutes — this stage does not mint one.
        //
        // The model cannot state expect_ty exactly: `IRScalar` carries no type
        // tag (an `int_ n` does not say its width, an `aggv` does not say its
        // id), which is the same design choice that lets a cell hold a value
        // rather than a byte image. What it CAN decide is the SHAPE class, and
        // that is what this checks. The residual — two integers of different
        // widths or signedness, two aggregates of different ids — is the
        // declared delta `copy-type-check-coarse`. The residual is TWO-WAY and
        // both directions are declared; reference lines read at trust
        // 0dd9d3e2d7. ACCEPT-MORE: a width, signedness or aggregate-id
        // disagreement passes the shape check and would fail expect_ty
        // (interpret.rs:5548-5557). REJECT-MORE, and fail-closed: the
        // reference's Copy arm never calls reject_partial
        // (interpret.rs:691-696; reject_partial is interpret.rs:6506-6515 and
        // its own message, interpret.rs:6500-6501, states that poison "may
        // only be copied or stored, never inspected"), so it transports poison
        // VERBATIM where `ir_copy_eval` faults type_error at
        // `ir_scalar_shape`'s class 0 — no `ir_ty_shape` is zero. That half is
        // unreachable on the executed fragment: the model's only producer of a
        // bound `undef_` is `IRInst.undef`, itself the declared delta
        // `undef-execution`, and an unwritten alloca cell is UB to load rather
        // than a bound value.
        // ===================================================================
        self.add_recursive_def(
            r"def ir_ty_shape (t : IRTy) : Nat := match t with
| IRTy.bool_ => Nat.succ Nat.zero
| IRTy.int_ w => Nat.succ (Nat.succ Nat.zero)
| IRTy.uint_ w => Nat.succ (Nat.succ Nat.zero)
| IRTy.float_ w => Nat.succ (Nat.succ (Nat.succ Nat.zero))
| IRTy.ptr_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRTy.ref_ p => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRTy.refmut_ p => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRTy.rawconst_ p => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRTy.rawmut_ p => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRTy.rc_ p => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRTy.fatptr_ p => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
| IRTy.unit_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
| IRTy.never_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))
| IRTy.tuple_ k => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
| IRTy.array_ p k => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
| IRTy.struct_ k => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
| IRTy.enum_ k => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
| IRTy.func_ k => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))
| IRTy.usize_ bits => 10
| IRTy.fatstr_ => 10
| IRTy.fatslice_ element => 10
| IRTy.fatdyn_ traitId => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
| IRTy.containerlen_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
| IRTy.containervtable_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))",
            "The value-shape class a declared type admits: 1 bool, 2 integer (either \
             signedness, any width), 3 float, 4 thin pointer (the whole ref/raw/rc family), 5 \
             fat pointer, 6 unit, 7 aggregate (tuple/array/struct/enum), 8 function pointer, 9 \
             never (uninhabited — no scalar class matches it). Coarser than trust_ir::Ty \
             equality on purpose: the model's scalars carry no width or id, so this is the \
             finest partition it can DECIDE. Crystal E5 (memo §23): the trait-object and the \
             two container-tail kinds (`fatdyn_`, `containerlen_`, `containervtable_`) are fat \
             pointers, class 5 beside the legacy `fatptr_`, because their value is the same \
             `IRScalar.fat_` (data address, metadata word) the reference's `FatPtr` value is; \
             the other appended ByteV1 kinds (`usize_`, `fatstr_`, `fatslice_`) keep class 10, \
             which no value inhabits, since the cell projector never emits them.",
        )?;

        self.add_recursive_def(
            r"def ir_scalar_shape (v : IRScalar) : Nat := match v with
| IRScalar.undef_ => Nat.zero
| IRScalar.bool_ b => Nat.succ Nat.zero
| IRScalar.int_ n => Nat.succ (Nat.succ Nat.zero)
| IRScalar.float_ n => Nat.succ (Nat.succ (Nat.succ Nat.zero))
| IRScalar.unit_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
| IRScalar.ptr_ a => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRScalar.nullptr_ => Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
| IRScalar.fat_ d md => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
| IRScalar.fnptr_ f => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))
| IRScalar.aggv sp => Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
| IRScalar.vnil => Nat.zero
| IRScalar.vcons x rest => Nat.zero",
            "The shape class a value inhabits, on the same scale as ir_ty_shape. Class 0 is \
             `matches nothing`: poison (which the reference reaches through reject_partial \
             wherever it inspects content) and the two bare spine constructors, which are \
             element-list nodes and not values of any type — the same fail-closed reading \
             ir_const_eval gives them.",
        )?;

        self.add_recursive_def(
            r"def ir_ty_fault (t : IRTy) : IRFault := match t with
| IRTy.bool_ => IRFault.not_bool
| IRTy.int_ w => IRFault.not_int
| IRTy.uint_ w => IRFault.not_int
| IRTy.float_ w => IRFault.not_float
| IRTy.ptr_ => IRFault.not_ptr
| IRTy.ref_ p => IRFault.not_ptr
| IRTy.refmut_ p => IRFault.not_ptr
| IRTy.rawconst_ p => IRFault.not_ptr
| IRTy.rawmut_ p => IRFault.not_ptr
| IRTy.rc_ p => IRFault.not_ptr
| IRTy.fatptr_ p => IRFault.not_ptr
| IRTy.unit_ => IRFault.not_agg
| IRTy.never_ => IRFault.not_agg
| IRTy.tuple_ k => IRFault.not_agg
| IRTy.array_ p k => IRFault.not_agg
| IRTy.struct_ k => IRFault.not_agg
| IRTy.enum_ k => IRFault.not_agg
| IRTy.func_ k => IRFault.not_fnptr
| IRTy.usize_ bits => IRFault.not_int
| IRTy.fatstr_ => IRFault.not_ptr
| IRTy.fatslice_ element => IRFault.not_ptr
| IRTy.fatdyn_ traitId => IRFault.not_ptr
| IRTy.containerlen_ => IRFault.not_ptr
| IRTy.containervtable_ => IRFault.not_ptr",
            "The fault CLASS a type mismatch reports, taken from the DECLARED type — the \
             convention ir_const_int_eval (not_int at a non-integral type) and ir_const_agg_eval \
             (not_agg at a non-aggregate type) already follow, and the class the reference's own \
             expect_* helpers report.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_copy_eval (t : IRTy) (v : IRScalar) : IRStepResult := ",
                "@Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error (ir_ty_fault t))) ",
                "(IRStepResult.value v) ",
                "(ir_nat_eqb (ir_ty_shape t) (ir_scalar_shape v))",
            ),
            "Copy: the reference's `expect_ty` then a rebind of the same value. The check is at \
             SHAPE granularity (the finest the model can decide), so it faults on every \
             mismatch the reference's dynamic type equality would fault on ACROSS classes and \
             accepts within one — a width or an aggregate id disagreement passes here and would \
             not there. That gap is the declared delta `copy-type-check-coarse`, and it is the \
             reason this stage mints no irrelevance theorem for `copy.t`.",
        )?;

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
| IRMemSlot.mk a v live => @Bool.rec (fun (_ : Bool) => IRStepResult) (IRStepResult.fault (IROutcome.ub IRFault.bad_addr)) (ir_load_value v) live",
            "Load from a cell, refusing a dead one. Bool.rec minor order is (false, true), so the \
             first minor is the dead case.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_load_slot (o : IROption IRMemSlot) : IRStepResult := ",
                "@IROption.rec IRMemSlot (fun (_ : IROption IRMemSlot) => IRStepResult) ",
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
                "@Bool.rec (fun (_ : Bool) => IRConfig) ",
                "(IRConfig.halted (IROutcome.ub IRFault.bad_addr)) ",
                "(ir_advance (ir_set_mem s (ir_mem_update (ir_mach_mem s) a v))) ",
                "live",
            ),
            "Commit a store to a live cell.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_store_checked (s : IRMachine) (a : Nat) (v : IRScalar) (o : IROption IRMemSlot) : IRConfig := ",
                "@IROption.rec IRMemSlot (fun (_ : IROption IRMemSlot) => IRConfig) ",
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
                "@Nat.rec (fun (_ : Nat) => IRList IRMemSlot) mem ",
                "(fun (j : Nat) (ih : IRList IRMemSlot) => ",
                "@IRList.cons IRMemSlot (IRMemSlot.mk (Nat.add base j) IRScalar.undef_ Bool.true) ih) k",
            ),
            "Create k live, uninitialised cells at base .. base+k-1. Uninitialised is undef_, and \
             loading undef_ is UB, so an unwritten allocation cannot be read as a value.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_alloca_k (s : IRMachine) (rs : IRList Nat) (k : Nat) : IRConfig := ",
                "@IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(@IRList.cons IRFrame (ir_frame_bind f rs (IRScalar.ptr_ na)) rest) ",
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
                "@IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) ",
                "(@IROption.some Nat (Nat.succ Nat.zero)) ",
                "(fun (i : Nat) => ir_as_int (ir_getd s i)) c",
            ),
            "Alloca's element count: absent means one, present means the integer value of that \
             SSA operand.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_alloca_exec (s : IRMachine) (rs : IRList Nat) (c : IROption Nat) : IRConfig := ",
                "@IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_int)) ",
                "(fun (k : Nat) => ir_alloca_k s rs k) (ir_alloca_count s c)",
            ),
            "Alloca.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_opt_add (a : IROption Nat) (b : IROption Nat) : IROption Nat := ",
                "@IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) (@IROption.none Nat) ",
                "(fun (x : Nat) => @IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat) ",
                "(@IROption.none Nat) (fun (y : Nat) => @IROption.some Nat (Nat.add x y)) b) a",
            ),
            "Addition lifted over partiality, for GEP's index sum.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_sum_idx (l : IRList IRScalar) : IROption Nat := ",
                "@IRList.rec IRScalar (fun (_ : IRList IRScalar) => IROption Nat) ",
                "(@IROption.some Nat Nat.zero) ",
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
                "@IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
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

        // ===================================================================
        // Crystal E5 (memo §23): the metadata lane is TYPED by the node's
        // declared metadata type, as the reference's is.
        //
        // `IRScalar.fat_ d md` carries its metadata as a bare word; what the
        // word MEANS is fixed by the kind, and the reference reads it back at
        // the kind's canonical metadata type (`FatPtrKind::metadata_ty`, trust-ir
        // shape.rs): a pointer-sized UNSIGNED length for `Slice`/`Str`/
        // `ContainerLen`, a thin `Ty::Ptr` VTABLE word for `TraitObject`/
        // `ContainerVtable` (interpret.rs `eval_ptr_metadata`, which also refuses
        // a declared metadata type that is not that canonical one). Until E5 this
        // arm bound `int_ md` for EVERY fat value, so a vtable word came back an
        // integer and D14's `gep` on it halted `type_error not_ptr` where the
        // reference proceeds (memo §21 E-b). Now the declared type decides:
        // `uint_ w` binds the length, `ptr_` binds the vtable address, and every
        // other type is the reference's type error. Thin values keep their
        // unit arm and do not consult the type (unchanged; the reference's
        // `metadata_ty == ()` check for a thin pointer is the pre-existing
        // coarseness of this machine, not an E5 row).
        // ===================================================================
        self.add_recursive_def(
            r"def ir_ptrmeta_lane (mt : IRTy) (md : Nat) : IRStepResult := match mt with
| IRTy.bool_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.int_ w => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.uint_ w => IRStepResult.value (IRScalar.int_ md)
| IRTy.float_ w => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.ptr_ => IRStepResult.value (IRScalar.ptr_ md)
| IRTy.ref_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.refmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.rawconst_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.rawmut_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.rc_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.fatptr_ p => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.never_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.tuple_ k => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.array_ p k => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.struct_ k => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.enum_ k => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.func_ k => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.usize_ bits => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.fatstr_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.fatslice_ element => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.fatdyn_ traitId => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.containerlen_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRTy.containervtable_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "Crystal E5: a fat value's metadata word read at the node's DECLARED metadata type. \
             An unsigned integer type binds the word as a length (`int_`), the thin pointer type \
             binds it as a vtable ADDRESS (`ptr_`), and every other type is a type_error — the \
             reference's canonical-metadata check (`eval_ptr_metadata`: a length for Slice/Str/\
             ContainerLen, a thin Ptr for TraitObject/ContainerVtable).",
        )?;

        self.add_recursive_def(
            r"def ir_ptrmeta_eval (mt : IRTy) (p : IRScalar) : IRStepResult := match p with
| IRScalar.undef_ => IRStepResult.value IRScalar.undef_
| IRScalar.bool_ b => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.int_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.float_ n => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.unit_ => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.ptr_ a => IRStepResult.value IRScalar.unit_
| IRScalar.nullptr_ => IRStepResult.value IRScalar.unit_
| IRScalar.fat_ d md => ir_ptrmeta_lane mt md
| IRScalar.fnptr_ f => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.aggv sp => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vnil => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)
| IRScalar.vcons x rest => IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)",
            "PtrMetadata: unit for a thin pointer, the metadata word for a wide one — the \
             thin-vs-fat dispatch that is why IRTy keeps its pointee — and since crystal E5 the \
             wide one's word is read at the DECLARED metadata type (`ir_ptrmeta_lane`): a length \
             at an unsigned type, a vtable address at `ptr_`.",
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
                "@IROption.rec IRScalar (fun (_ : IROption IRScalar) => IRStepResult) ",
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
                "@IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
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
                "@Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.bad_field)) ",
                "(IRStepResult.value (IRScalar.aggv (ir_vals_set sp k v))) ",
                "(ir_nat_ltb k (ir_vals_len sp))",
            ),
            "Field write into an aggregate's spine, rebuilding the whole value. @Bool.rec minor \
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
                "@IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(@IRList.cons IRFrame ",
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
                "@IROption.rec IRBlock (fun (_ : IROption IRBlock) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_block)) ",
                "(fun (b : IRBlock) => ir_goto s tgt (ir_block_params b) vs) ob",
            ),
            "Jump to a resolved block.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_jump_func (s : IRMachine) (tgt : Nat) (vs : IRList IRScalar) (of : IROption IRFunc) : IRConfig := ",
                "@IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_func)) ",
                "(fun (f : IRFunc) => ir_jump_block s tgt vs (ir_block_find (ir_func_blocks f) tgt)) of",
            ),
            "Jump within a resolved function.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_cur_func (m : IRModule) (s : IRMachine) : IROption IRFunc := ",
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IROption IRFunc) ",
                "(@IROption.none IRFunc) ",
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
                "@Bool.rec (fun (_ : Bool) => IRConfig) ",
                "(ir_jump m s et eargs) (ir_jump m s tt targs) b",
            ),
            "CondBr on a decided condition. @Bool.rec minor order is (false, true), so the first \
             minor is the else edge.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_condbr_exec (m : IRModule) (s : IRMachine) (c : IRScalar) (tt : Nat) ",
                "(targs : IRList Nat) (et : Nat) (eargs : IRList Nat) : IRConfig := ",
                "@IROption.rec Bool (fun (_ : IROption Bool) => IRConfig) ",
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
                "@IROption.rec IRSwitchCase (fun (_ : IROption IRSwitchCase) => IRConfig) ",
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
                "@IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_int)) ",
                "(fun (n : Nat) => ir_switch_n m s dflt dargs cases n) (ir_as_int v)",
            ),
            "Switch.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_push (s : IRMachine) (rs : IRList Nat) (f : IRFunc) (vs : IRList IRScalar) : IRConfig := ",
                "@IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (cur : IRFrame) (rest : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(@IRList.cons IRFrame ",
                "(IRFrame.mk (ir_func_id f) (ir_func_entry f) Nat.zero ",
                "(ir_bind_params (ir_func_params f) vs (@IRList.nil IRBinding)) rs) ",
                "(@IRList.cons IRFrame (ir_frame_advance cur) rest)) ",
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
                "@IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) ",
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
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.ret vs)) ",
                "(fun (caller : IRFrame) (rest2 : IRList IRFrame) (_ : IRConfig) => ",
                "IRConfig.running (IRMachine.mk ",
                "(@IRList.cons IRFrame (ir_frame_set_many caller dests vs) rest2) mem na)) ",
                "rest",
            ),
            "Pop to the caller, binding the returned values positionally to the call node's \
             declared result ids — so a multi-value return needs no packing and loses nothing. \
             When the outermost frame returns, halt with the returned values.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_ret_vals (s : IRMachine) (vs : IRList IRScalar) : IRConfig := ",
                "@IRMachine.rec (fun (_ : IRMachine) => IRConfig) ",
                "(fun (fs : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) => ",
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
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
                "@Bool.rec (fun (_ : Bool) => IRConfig) ",
                "(IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_advance s) b",
            ),
            "Assert on a decided condition: a false assertion is UB, which is how a Rust panic \
             path shows up in this model.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_assert_exec (s : IRMachine) (c : IRScalar) : IRConfig := ",
                "@IROption.rec Bool (fun (_ : IROption Bool) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (b : Bool) => ir_assert_b s b) (ir_as_bool c)",
            ),
            "Assert.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_select_eval (c : IRScalar) (a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "@IROption.rec Bool (fun (_ : IROption Bool) => IRStepResult) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_bool)) ",
                "(fun (x : Bool) => @Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "(IRStepResult.value b) (IRStepResult.value a) x) (ir_as_bool c)",
            ),
            "Select: the branch-free conditional. @Bool.rec minor order is (false, true).",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_globaladdr_eval (m : IRModule) (g : Nat) : IRStepResult := ",
                "@IROption.rec IRGlobal (fun (_ : IROption IRGlobal) => IRStepResult) ",
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

    /// Overflow — the checked-arithmetic instruction's two-result execution
    /// (plan W3, 2026-08-25). The value math lives in
    /// [`super::eval_ir_ops`] (`ir_overflow_value` / `ir_overflow_flag`);
    /// this layer coerces the operands, dispatches the type's signedness, and
    /// binds the pair through `ir_bind2` — the config-level pattern
    /// (`ir_store_exec` / `ir_alloca_exec`), which is how the plan's
    /// recommended design α (two results bound positionally through the
    /// existing `ir_bind_params` multi-bind, the `ir_ret_to` precedent) lands
    /// WITHOUT a new `IRStepResult2` inductive: `IRStepResult` stays
    /// single-valued, the vacuity firewall's family list stays untouched by
    /// construction, and the success continuation produces the configuration
    /// directly.
    fn add_eval_ir_overflow(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_overflow_ints (s : IRMachine) (rs : IRList Nat) (op : IROverflowOp) ",
                "(sgn : Bool) (w : Nat) (x : Nat) (y : Nat) : IRConfig := ",
                "ir_bind2 s rs ",
                "(IRScalar.int_ (ir_overflow_value op w (ir_wrap w x) (ir_wrap w y))) ",
                "(IRScalar.bool_ (ir_overflow_flag op sgn w (ir_wrap w x) (ir_wrap w y)))",
            ),
            "Overflow on decided integers: bind (wrapped value, flag) at the node's two \
             declared result ids. Operands are wrapped to canonical width-w residues ONCE \
             here — the ir_uint2 / ir_int2_width_result discipline — so a junk over-wide \
             int_ cannot leak a wrong flag; trust-ir's InterpretInt.raw is always masked, so \
             on every reachable value the wrap is the identity. The result pair is exactly \
             a4e81b6 interpret.rs:640-642's [result, InterpretValue::bool(overflow)].",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_overflow_vals (s : IRMachine) (rs : IRList Nat) (op : IROverflowOp) ",
                "(sgn : Bool) (w : Nat) (a : IRScalar) (b : IRScalar) : IRConfig := ",
                "@IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_int)) ",
                "(fun (x : Nat) => @IROption.rec Nat (fun (_ : IROption Nat) => IRConfig) ",
                "(IRConfig.halted (IROutcome.type_error IRFault.not_int)) ",
                "(fun (y : Nat) => ir_overflow_ints s rs op sgn w x y) (ir_as_int b)) ",
                "(ir_as_int a)",
            ),
            "Overflow's operand coercion — ir_int2's shape at config level: any non-integer \
             operand (undef_, a Bool, a pointer, an aggregate) fails closed with type_error \
             not_int, the same CLASS the reference interpreter's expect_int_value reports \
             (a4e81b6 interpret.rs:5429-5434, which rejects Bool too — i1 checked arithmetic \
             does not exist on either side).",
        )?;

        self.add_recursive_def(
            r"def ir_overflow_exec (s : IRMachine) (rs : IRList Nat) (op : IROverflowOp) (t : IRTy) (a : IRScalar) (b : IRScalar) : IRConfig := match t with
| IRTy.int_ w => ir_overflow_vals s rs op Bool.true w a b
| IRTy.uint_ w => ir_overflow_vals s rs op Bool.false w a b
| _ => IRConfig.halted (IROutcome.type_error IRFault.not_int)",
            "Overflow: the type dispatch. int_ selects the signed flag, uint_ the unsigned \
             one — the signedness the constructor choice encodes is SEMANTIC input here, \
             exactly as trust-ir dispatches eval_int_overflow on InterpretInt.signed \
             (a4e81b6 interpret.rs:5872-5876). Every other type — bool_ included — fails \
             closed with type_error not_int, matching the interpreter's expect_ty + \
             expect_int_value rejections at class.",
        )?;

        Ok(())
    }

    /// The exhaustive dispatch, the fetch step, and the fuel-driven driver.
    fn add_eval_ir_dispatch(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def ir_exec (m : IRModule) (i : IRInst) (rs : IRList Nat) (s : IRMachine) : IRConfig := match i with
| IRInst.binop op t a b => ir_bind_result s rs (ir_binop_eval op t (ir_getd s a) (ir_getd s b))
| IRInst.unop op t a => ir_bind_result s rs (ir_unop_eval op t (ir_getd s a))
| IRInst.overflow op t a b => ir_overflow_exec s rs op t (ir_getd s a) (ir_getd s b)
| IRInst.icmp op t a b => ir_bind_result s rs (ir_icmp_eval op t (ir_getd s a) (ir_getd s b))
| IRInst.fcmp op t a b => ir_bind_result s rs (ir_fcmp_eval op t (ir_getd s a) (ir_getd s b))
| IRInst.cast op sr ds a => ir_bind_result s rs (ir_cast_eval op sr ds (ir_getd s a))
| IRInst.load t p vol => ir_bind_result s rs (ir_load_view (ir_mod_encs m) t (ir_load_eval s (ir_getd s p)))
| IRInst.store t p v vol => ir_store_exec s (ir_getd s p) (ir_getd s v)
| IRInst.alloca t c => ir_alloca_exec s rs c
| IRInst.gep t b idxs inb => ir_bind_result s rs (ir_gep_eval (ir_getd s b) (ir_resolve s idxs))
| IRInst.ptrdata t p => ir_bind_result s rs (ir_ptrdata_eval (ir_getd s p))
| IRInst.ptrmetadata pt mt p => ir_bind_result s rs (ir_ptrmeta_eval mt (ir_getd s p))
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
| IRInst.select t c a b => ir_bind_result s rs (ir_select_eval (ir_getd s c) (ir_getd s a) (ir_getd s b))
| IRInst.borrow p => ir_bind_result s rs (ir_borrow_eval (ir_mach_mem s) (ir_getd s p))
| IRInst.copy t a => ir_bind_result s rs (ir_copy_eval t (ir_getd s a))
| IRInst.atomic_fetch_add_relaxed_u64_seq pointer value => IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)
| IRInst.atomic_fetch_add_relaxed_usize_seq bits pointer value => IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)
| IRInst.release pointer => IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)",
            "THE COVERAGE CLAIM: 33 explicit arms: thirty legacy modelled fragments, two \
             named refusals for sequential byte fetch-add and one for retained Release syntax. TWO modelled arms arrived with Phase B from the OTHER producer (the trust-ir \
             bridge, not the THIR lowerer): `borrow`, whose reference arm is a \
             dereference-time provenance check and is modelled as one, and `copy`, whose \
             declared type the reference READS to decide accept-versus-fault and which is \
             therefore modelled rather than dropped. The `load` arm now consults the module's \
             DERIVED encodings table; on every module minted before Phase B that table is \
             empty and the arm iota-reduces to the pre-Phase-B one. The appended \
             atomic_fetch_add_relaxed_u64_seq and atomic_fetch_add_relaxed_usize_seq arms \
             are unmodelled width_bounded: the legacy cell model cannot execute their \
             byte-width-sensitive memory operations. Their operands are deliberately \
             unread because EVERY instance is refused; \
             this is neither execution coverage nor an atomic safety assumption. Apart from those explicit refusals, every \
             other arm has real semantics on its declared fragment (the residue is operator/fragment-level and stays tagged \
             fail-closed inside the evaluators — the eval_ir_state exclusion table is the \
             list). This sentence has been counted down in the open: \"exactly two\" until \
             2026-08-25 (overflow's arm, replaced by the W3 wave with ir_overflow_exec's \
             two-result semantics — value + flag bound positionally through ir_bind2), then \
             \"exactly one\" for fcmp, replaced the same day by the W4 wave with \
             ir_fcmp_eval's 12 real predicates over the classified binary64 substrate — \
             note the arm now PASSES `t`, which the pre-W4 dispatch dropped: the fcmp type \
             is semantic input (the width gate), exactly as in the binop arm. No arm is a \
             catch-all and none is missing, so the fraction is checkable constructor by \
             constructor. Dated extension 2026-09-24: the byte-only atomic constructors add \
             two explicit legacy refusals. Release syntax adds the third on 2026-11-08; the prior zero-whole-arm-refusals claim applies \
             only to the thirty-constructor legacy scope.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_exec_atomic_fetch_add_relaxed_u64_seq_unmodelled ",
                "(m : IRModule) (pointer : Nat) (value : Nat) (rs : IRList Nat) ",
                "(s : IRMachine) : @Eq IRConfig ",
                "(ir_exec m (IRInst.atomic_fetch_add_relaxed_u64_seq pointer value) rs s) ",
                "(IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)) := ",
                "@Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            ),
            "Universal LEGACY REFUSAL: sequential byte fetch-add halts unmodelled at every \
             module, pointer id, increment id, result list and machine. No successful-result \
             premise, memory transition, atomic admission or concurrency claim. The byte \
             executor is a separate profile; this theorem says only what the cell executor \
             refuses. @Eq.refl proof term, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_exec_atomic_fetch_add_relaxed_u64_seq_pointer_irrelevant ",
                "(m : IRModule) (pointer1 : Nat) (pointer2 : Nat) (value : Nat) ",
                "(rs : IRList Nat) (s : IRMachine) : @Eq IRConfig ",
                "(ir_exec m (IRInst.atomic_fetch_add_relaxed_u64_seq pointer1 value) rs s) ",
                "(ir_exec m (IRInst.atomic_fetch_add_relaxed_u64_seq pointer2 value) rs s) := ",
                "@Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            ),
            "Legacy REFUSAL independence only: varying the pointer leaves the same universal \
             unmodelled outcome. This accounts for the unread field in ir_exec, not for the \
             byte executor, where the pointer determines the actual memory operation. It \
             grants no successful-execution coverage. @Eq.refl proof term, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_exec_atomic_fetch_add_relaxed_u64_seq_value_irrelevant ",
                "(m : IRModule) (pointer : Nat) (value1 : Nat) (value2 : Nat) ",
                "(rs : IRList Nat) (s : IRMachine) : @Eq IRConfig ",
                "(ir_exec m (IRInst.atomic_fetch_add_relaxed_u64_seq pointer value1) rs s) ",
                "(ir_exec m (IRInst.atomic_fetch_add_relaxed_u64_seq pointer value2) rs s) := ",
                "@Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            ),
            "Legacy REFUSAL independence only: varying the increment leaves the same universal \
             unmodelled outcome. This accounts for the unread field in ir_exec, not for the \
             byte executor, where the increment determines the stored value. It grants no \
             successful-execution coverage. @Eq.refl proof term, zero axiom_deps.",
        )?;

        // ===================================================================
        // Usize is also byte-only. These universal refusal equalities account
        // for unread legacy operands without claiming successful execution.
        self.add_recursive_def(
            "def ir_exec_atomic_fetch_add_relaxed_usize_seq_unmodelled (m : IRModule) (bits pointer value : Nat) (rs : IRList Nat) (s : IRMachine) : @Eq IRConfig (ir_exec m (IRInst.atomic_fetch_add_relaxed_usize_seq bits pointer value) rs s) (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)) := @Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            "Universal legacy Usize atomic refusal, not successful execution or source authority.",
        )?;
        self.add_recursive_def(
            "def ir_exec_atomic_fetch_add_relaxed_usize_seq_bits_irrelevant (m : IRModule) (bits1 bits2 pointer value : Nat) (rs : IRList Nat) (s : IRMachine) : @Eq IRConfig (ir_exec m (IRInst.atomic_fetch_add_relaxed_usize_seq bits1 pointer value) rs s) (ir_exec m (IRInst.atomic_fetch_add_relaxed_usize_seq bits2 pointer value) rs s) := @Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            "Unread legacy width: equality of explicit refusals only.",
        )?;
        self.add_recursive_def(
            "def ir_exec_atomic_fetch_add_relaxed_usize_seq_pointer_irrelevant (m : IRModule) (bits pointer1 pointer2 value : Nat) (rs : IRList Nat) (s : IRMachine) : @Eq IRConfig (ir_exec m (IRInst.atomic_fetch_add_relaxed_usize_seq bits pointer1 value) rs s) (ir_exec m (IRInst.atomic_fetch_add_relaxed_usize_seq bits pointer2 value) rs s) := @Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            "Unread legacy pointer: equality of explicit refusals only.",
        )?;
        self.add_recursive_def(
            "def ir_exec_atomic_fetch_add_relaxed_usize_seq_value_irrelevant (m : IRModule) (bits pointer value1 value2 : Nat) (rs : IRList Nat) (s : IRMachine) : @Eq IRConfig (ir_exec m (IRInst.atomic_fetch_add_relaxed_usize_seq bits pointer value1) rs s) (ir_exec m (IRInst.atomic_fetch_add_relaxed_usize_seq bits pointer value2) rs s) := @Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            "Unread legacy increment: equality of explicit refusals only.",
        )?;

        self.add_recursive_def(
            "def ir_exec_release_unmodelled (m : IRModule) (pointer : Nat) (rs : IRList Nat) (s : IRMachine) : @Eq IRConfig (ir_exec m (IRInst.release pointer) rs s) (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded)) := @Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            "Universal legacy Release refusal only; no reference count, pointer or successful execution semantics.",
        )?;
        self.add_recursive_def(
            "def ir_exec_release_pointer_irrelevant (m : IRModule) (pointer1 pointer2 : Nat) (rs : IRList Nat) (s : IRMachine) : @Eq IRConfig (ir_exec m (IRInst.release pointer1) rs s) (ir_exec m (IRInst.release pointer2) rs s) := @Eq.refl IRConfig (IRConfig.halted (IROutcome.unmodelled IRFault.width_bounded))",
            "Unread pointer in the explicit legacy refusal; no irrelevance claim about Rust Release.",
        )?;

        // THE THREE OPERANDS THE DISPATCH DROPS, PROVED INERT.
        //
        // DATED CORRECTION (2026-08-25, plan W5): "exactly three" below was
        // the operand-audit-era reading. The mechanical derivation over the
        // whole dispatch (`scripts/evalir_adequacy_grid.py`, gated by
        // `tests/eval_ir/adequacy_grid.rs`) counts NINETEEN bound-and-dropped
        // fields; these three theorems are the precedent, and the other
        // sixteen — the type annotations, volatility flags and
        // `gep.inbounds` — live in `eval_ir_adequacy.rs`, registered at the
        // end of this stage, same `Eq.refl` mechanism. The full
        // per-constructor account is `data/evalir_adequacy_grid.json`.
        //
        // It was TWENTY until Phase B: `load.t` left the set when the load arm
        // started consulting the module's encodings table, and the two
        // constructors Phase B added contribute no dropped field at all —
        // `borrow.p` and `copy.a` are read as operands, and `copy.t` is read
        // by the type check the reference's own arm performs.
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
                "(s : IRMachine) : @Eq IRConfig ",
                "(ir_exec m (IRInst.switch v dflt dargs cases Bool.true) rs s) ",
                "(ir_exec m (IRInst.switch v dflt dargs cases Bool.false) rs s) := ",
                "@Eq.refl IRConfig (ir_switch_exec m s (ir_getd s v) dflt dargs cases)",
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
                "@Eq IRConfig (ir_exec m (IRInst.callindirect cid sig args cc1) rs s) ",
                "(ir_exec m (IRInst.callindirect cid sig args cc2) rs s) := ",
                "@Eq.refl IRConfig (ir_callind_exec m s rs (ir_getd s cid) args)",
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
                "@Eq IRConfig (ir_exec m (IRInst.callindirect cid g1 args cc) rs s) ",
                "(ir_exec m (IRInst.callindirect cid g2 args cc) rs s) := ",
                "@Eq.refl IRConfig (ir_callind_exec m s rs (ir_getd s cid) args)",
            ),
            "ir_exec_callind_sig_irrelevant: the SIGNATURE-TABLE index cannot change the step \
             either. That index is the same whole-crate `functy.N` the header carries and the \
             `functy-index` blind slot names — measured to renumber on every producer change with \
             no instruction changed — so this is the kernel-checked reason the core module may \
             drop it. DerivedProved, zero axiom_deps.",
        )?;

        // ===================================================================
        // THE LOAD ARM'S TWO PHASE-B WITNESSES.
        //
        // The arm now reads the load's TYPE, through the module's derived
        // encodings table. Two facts have to be on the wire rather than in
        // prose, and they point in opposite directions:
        //
        //  * CONSERVATIVITY. On an `IRModule.mk` — every module minted before
        //    Phase B, all eighteen chains — the table is empty, the view is
        //    the identity, and the type is still irrelevant. That is
        //    `ir_exec_load_ty_irrelevant_mk`, an `Eq.refl` whose reduct is the
        //    PRE-Phase-B arm verbatim.
        //  * THE ARM REALLY READS IT. On an `IRModule.mkv` carrying one row,
        //    the same load at the SAME pointer produces a decoded aggregate
        //    rather than the stored word. That is `ir_load_view_mkv_reads_ty`,
        //    the negative witness the general theorem cannot have: it exhibits
        //    a module and a type at which the view is not the identity, so
        //    "the type is dropped" is refuted by execution and not merely
        //    unstated.
        // ===================================================================
        self.add_recursive_def(
            concat!(
                "def ir_exec_load_ty_irrelevant_mk (fs : IRList IRFunc) (gs : IRList IRGlobal) ",
                "(t1 : IRTy) (t2 : IRTy) (p : Nat) (vol : Bool) (rs : IRList Nat) ",
                "(s : IRMachine) : @Eq IRConfig ",
                "(ir_exec (IRModule.mk fs gs) (IRInst.load t1 p vol) rs s) ",
                "(ir_exec (IRModule.mk fs gs) (IRInst.load t2 p vol) rs s) := ",
                "@Eq.refl IRConfig (ir_bind_result s rs (ir_load_eval s (ir_getd s p)))",
            ),
            "ir_exec_load_ty_irrelevant_mk: CONSERVATIVITY, stated as the theorem the general \
             one used to be. At a module with no encodings table the load's type cannot change \
             the step at any two types, any pointer, any volatility, any state — and the proof \
             term is the pre-Phase-B dispatch arm itself, so the kernel is checking that the \
             encoding-aware arm REDUCES to the old one rather than merely agreeing with it. \
             Every chain minted before Phase B is an IRModule.mk. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_load_view_mkv_reads_ty (b : Nat) : @Eq IRStepResult ",
                "(ir_load_view (ir_mod_encs (IRModule.mkv (@IRList.nil IRFunc) (@IRList.nil IRGlobal) ",
                "(@IRList.cons IREnc (IREnc.nicheptr Nat.zero Nat.zero (Nat.succ Nat.zero) IRTy.ptr_) ",
                "(@IRList.nil IREnc)))) (IRTy.enum_ Nat.zero) ",
                "(IRStepResult.value (IRScalar.ptr_ (Nat.succ b)))) ",
                "(IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ (Nat.succ Nat.zero)) ",
                "(IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil)))) := ",
                "@Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv ",
                "(IRScalar.vcons (IRScalar.int_ (Nat.succ Nat.zero)) ",
                "(IRScalar.vcons (IRScalar.ptr_ (Nat.succ b)) IRScalar.vnil))))",
            ),
            "ir_load_view_mkv_reads_ty: THE NEGATIVE WITNESS. At a module whose table has one \
             nicheptr row for `enum 0`, loading at `IRTy.enum_ 0` a non-zero pointer word yields \
             the SOME image — tag at slot 0, payload at slot 1 — and not the word. So the load's \
             type is read, at an ABSTRACT base `b` (stated in successor form, since a \
             represented base is never the zero word). Pair it with \
             ir_exec_load_ty_irrelevant_mk: together they say the arm consults the table and \
             nothing else. DerivedProved, zero axiom_deps.",
        )?;

        // ===================================================================
        // THE TWO ARMS PHASE B ADDS, PINNED WHERE THEY DIVERGE FROM A NO-OP.
        //
        // Both `borrow` and `copy` would be the identity in a careless model,
        // and in BOTH cases the reference faults on inputs the identity would
        // accept. These are the two witnesses that the model faults there too.
        // ===================================================================
        self.add_recursive_def(
            concat!(
                "def ir_borrow_no_provenance_is_ub (a : Nat) : @Eq IRStepResult ",
                "(ir_borrow_eval (@IRList.nil IRMemSlot) (IRScalar.ptr_ a)) ",
                "(IRStepResult.fault (IROutcome.ub IRFault.bad_addr)) := ",
                "@Eq.refl IRStepResult (IRStepResult.fault (IROutcome.ub IRFault.bad_addr))",
            ),
            "ir_borrow_no_provenance_is_ub: borrowing an address with NO CELL is UB at every \
             address — the model's counterpart of the reference's `DanglingPtr` arm of \
             expect_pointer, which is reached whenever a pointer word read out of memory names \
             no allocation. This is the witness that the borrow arm is not the identity; \
             without it the model would continue where the reference stops, and the crystal \
             chain's own `Arc::deref` borrows exactly such a word. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_copy_ty_slot_is_read (n : Nat) : @Eq IRStepResult ",
                "(ir_copy_eval IRTy.ptr_ (IRScalar.int_ n)) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_ptr)) := ",
                "@Eq.refl IRStepResult (IRStepResult.fault (IROutcome.type_error IRFault.not_ptr))",
            ),
            "ir_copy_ty_slot_is_read: copying an integer AT A POINTER TYPE faults, at every \
             integer. That is why `copy.t` has no irrelevance theorem: the reference's arm calls \
             expect_ty and raises a type_error on disagreement, so the slot decides \
             accept-versus-fault and an irrelevance row would be an adequacy claim the reference \
             refutes. The model's check is coarser than expect_ty (declared delta \
             `copy-type-check-coarse`) but it is not absent. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_view_ptr0_is_none : @Eq IRStepResult ",
                "(ir_load_view (ir_mod_encs (IRModule.mkv (@IRList.nil IRFunc) (@IRList.nil IRGlobal) (@IRList.cons IREnc (IREnc.nicheptr Nat.zero Nat.zero (Nat.succ Nat.zero) IRTy.ptr_) (@IRList.nil IREnc)))) (IRTy.enum_ Nat.zero) ",
                "(IRStepResult.value (IRScalar.ptr_ Nat.zero))) ",
                "(IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ Nat.zero) IRScalar.vnil))) := ",
                "@Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv (IRScalar.vcons (IRScalar.int_ Nat.zero) IRScalar.vnil)))",
            ),
            "ir_view_ptr0_is_none: THE WORD-0 CLAUSE, executed. At a niche row the zero word is \
             the none variant — and Clean has two spellings of the zero word, so this pins the \
             `ptr_ Nat.zero` one (the `nullptr_` one is the same arm, read directly off \
             ir_niche_image). The reference computes the same answer by `relative = raw - \
             niche_start & mask` at niche_start 0 over an empty variant range, which is exactly \
             the shape the derivation rule refuses to mint a row without. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_view_agg_is_identity (sp : IRScalar) : @Eq IRStepResult ",
                "(ir_load_view (ir_mod_encs (IRModule.mkv (@IRList.nil IRFunc) (@IRList.nil IRGlobal) (@IRList.cons IREnc (IREnc.nicheptr Nat.zero Nat.zero (Nat.succ Nat.zero) IRTy.ptr_) (@IRList.nil IREnc)))) (IRTy.enum_ Nat.zero) ",
                "(IRStepResult.value (IRScalar.aggv sp))) ",
                "(IRStepResult.value (IRScalar.aggv sp)) := ",
                "@Eq.refl IRStepResult (IRStepResult.value (IRScalar.aggv sp))",
            ),
            "ir_view_agg_is_identity: at a MATCHED row, a cell holding an inline aggregate is \
             passed through unchanged, at every spine. The chain needs this — a stack slot \
             written with an aggregate and read back at its enum type must not be re-decoded as \
             a word — and it is also the honest statement of the view's partiality: the decode \
             is SHAPE-directed inside a type-directed dispatch, whereas the reference always \
             decodes the byte image it wrote. Recorded as the declared delta \
             `enum-load-shape-directed`. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            r"def ir_exec_node (m : IRModule) (n : IRNode) (s : IRMachine) : IRConfig := match n with
| IRNode.mk i rs => ir_exec m i rs s",
            "Execute a node: its instruction, with its declared result ids.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_step_n (m : IRModule) (s : IRMachine) (on : IROption IRNode) : IRConfig := ",
                "@IROption.rec IRNode (fun (_ : IROption IRNode) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.fetch_past_end)) ",
                "(fun (n : IRNode) => ir_exec_node m n s) on",
            ),
            "Execute a fetched node. Running off the end of a block is STUCK: a block without a \
             terminator does not fall through into its successor.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_step_b (m : IRModule) (s : IRMachine) (pc : Nat) (ob : IROption IRBlock) : IRConfig := ",
                "@IROption.rec IRBlock (fun (_ : IROption IRBlock) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_block)) ",
                "(fun (b : IRBlock) => ir_step_n m s (ir_nodes_get (ir_block_nodes b) pc)) ob",
            ),
            "Fetch within a resolved block.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_step_f (m : IRModule) (s : IRMachine) (bl : Nat) (pc : Nat) (of : IROption IRFunc) : IRConfig := ",
                "@IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) ",
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
                "@IRList.rec IRFrame (fun (_ : IRList IRFrame) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_frame)) ",
                "(fun (f : IRFrame) (_ : IRList IRFrame) (_ : IRConfig) => ir_step_frame m s f) ",
                "(ir_mach_frames s)",
            ),
            "One machine step.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_run (fuel : Nat) (m : IRModule) (c : IRConfig) : IROutcome := ",
                "@Nat.rec (fun (_ : Nat) => IRConfig -> IROutcome) ",
                "(fun (c0 : IRConfig) => @IRConfig.rec (fun (_ : IRConfig) => IROutcome) ",
                "(fun (_ : IRMachine) => IROutcome.fuel_out) (fun (o : IROutcome) => o) c0) ",
                "(fun (_ : Nat) (ih : IRConfig -> IROutcome) => fun (c0 : IRConfig) => ",
                "@IRConfig.rec (fun (_ : IRConfig) => IROutcome) ",
                "(fun (s : IRMachine) => ih (ir_step m s)) (fun (o : IROutcome) => o) c0) ",
                "fuel c",
            ),
            "Run to a halt or until the fuel runs out. Exhaustion is its OWN outcome, distinct \
             from every real result, so no theorem can mistake it for success.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_globals_mem (gs : IRList IRGlobal) : IRList IRMemSlot := ",
                "@IRList.rec IRGlobal (fun (_ : IRList IRGlobal) => IRList IRMemSlot) ",
                "(@IRList.nil IRMemSlot) ",
                "(fun (g : IRGlobal) (_ : IRList IRGlobal) (ih : IRList IRMemSlot) => ",
                "@IRGlobal.rec (fun (_ : IRGlobal) => IRList IRMemSlot) ",
                "(fun (i : Nat) (c : IRConst) => ",
                "@IRList.cons IRMemSlot (IRMemSlot.mk i (ir_const_value c) Bool.true) ih) g) gs",
            ),
            "Materialize one live cell per global, at the address that is its id.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_mem_concat (a : IRList IRMemSlot) (b : IRList IRMemSlot) : IRList IRMemSlot := ",
                "@IRList.rec IRMemSlot (fun (_ : IRList IRMemSlot) => IRList IRMemSlot) b ",
                "(fun (x : IRMemSlot) (_ : IRList IRMemSlot) (ih : IRList IRMemSlot) => ",
                "@IRList.cons IRMemSlot x ih) a",
            ),
            "Append two memories, globals first.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_init (m : IRModule) (fid : Nat) (args : IRList IRScalar) ",
                "(mem0 : IRList IRMemSlot) (na : Nat) : IRConfig := ",
                "@IROption.rec IRFunc (fun (_ : IROption IRFunc) => IRConfig) ",
                "(IRConfig.halted (IROutcome.stuck IRFault.no_func)) ",
                "(fun (f : IRFunc) => IRConfig.running (IRMachine.mk ",
                "(@IRList.cons IRFrame (IRFrame.mk (ir_func_id f) (ir_func_entry f) Nat.zero ",
                "(ir_bind_params (ir_func_params f) args (@IRList.nil IRBinding)) (@IRList.nil Nat)) ",
                "(@IRList.nil IRFrame)) ",
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
