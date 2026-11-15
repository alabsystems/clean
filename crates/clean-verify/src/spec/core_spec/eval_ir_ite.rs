// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`ir_ite` — `infer_type`'s transport tail, over the TARGET ALONE, at an
//! ARBITRARY heap, with NO callee named anywhere in the statement.**
//!
//! `ir_itd` proves the transport property by RUNNING the whole module, which
//! means its statement mentions two authored callees and pins the heap to
//! `ir_mem0`. That is the honest caller's-half result, and it is also the
//! weakest form of it: the models appear in the theorem, not merely in its
//! witnesses.
//!
//! This is the SEAM form. It starts from the configuration the machine is in
//! the instant `call 2` has returned — the `ir_hlb_resume` shape
//! (`eval_ir_has_loose_bvars.rs`), which never needs the callee to exist
//! because it begins after the callee is gone — and runs the four nodes that
//! remain:
//!
//! ```text
//!   b5:  store Result %2, %29     <- the value the inference returned
//!        br b3
//!   b3:  %5 = load Result %2
//!        ret %5
//! ```
//!
//! ```text
//!   forall a spv loc ds rest v0 mem na,
//!     ir_steps 4 ir_it_module (running (ir_ite_smach …))
//!       = ir_ret_to ds rest [ (a, aggv spv, live) :: mem ] na [ aggv spv ]
//! ```
//!
//! **The module is `ir_it_module` — `infer_type` and nothing else.** Every
//! authored model is gone from the statement. What remains quantified:
//!
//! * `spv` — the transported payload spine. The value is `IRScalar.aggv spv`
//!   rather than a bare variable because `ir_load_value` MATCHES on the scalar
//!   and is stuck at a neutral one; a head constructor is the weakest form that
//!   reduces, and it is the right one, since what `infer_type` transports is a
//!   `Result` aggregate.
//! * `mem` — the rest of the heap, `na` — the allocation counter, `rest` — the
//!   caller stack, `ds` — the caller's destination list, `loc` — whatever else
//!   the frame has bound, and `v0` — whatever the slot held before the store.
//!
//! The one thing ASSUMED rather than quantified is that the Result slot is LIVE
//! at the head of memory. That is the same assumption `ir_slot_activation`
//! carries and for the same mechanical reason: a head lookup resolves through
//! `ir_nat_eqb a a = true`, a Nat induction, where a lookup into an unknown
//! heap is stuck at a neutral operand. `infer_type` allocas that slot in `b0`
//! and nothing on the ok path allocates after it, so the head position is what
//! the body produces — but between the alloca and this store sits `call 2`,
//! and in the seam framing that callee is arbitrary and could allocate. So the
//! head position is stated as a hypothesis on the shape of `mem`, not proved.
//!
//! # What this does and does not add over `ir_itd`
//!
//! ADDS: the heap, the counter, the caller and the callee all leave the
//! statement. This says `infer_type`'s tail returns what it was handed, into
//! whatever heap, under whatever caller, with no model of the inference.
//!
//! DOES NOT ADD: it is a SEGMENT, not a run. Composing it back into an
//! end-to-end statement needs the dispatch seam (`b0`/`b1` at an abstract
//! heartbeat answer) and a composition step; until those land, `ir_itd` remains
//! the only end-to-end execution of this target and its two models remain its
//! stated residual. A4 is not claimed here either.
//!
//! **THE COMPOSITION STEP ALREADY EXISTS — corrected 2026-09-18.** The sentence
//! above lists two build items and only ONE of them is open. `ir_steps_add`
//! (registered) reads
//!
//! ```text
//! ir_steps (Nat.add b a) m c = ir_steps b m (ir_steps a m c)
//! ```
//!
//! which is exactly the additivity a composition needs, and `ir_run_steps_split`
//! sits beside it. Anyone scoping this should budget the SEAM alone.
//!
//! **And the seam is smaller than "b0/b1" suggests, but it cannot live at
//! `ir_it_module`.** `ir_ite_smach` places the machine at block 5 -- the ok path
//! -- at pc 1, i.e. AFTER `infer_type_fast` returned. So the seam has to carry
//! entry through `bb1`'s switch on an abstract heartbeat answer into `bb5`'s
//! call. But `ir_it_module` declares ONE function, so the heartbeat call goes
//! `stuck no_func` -- which is what `ir_it_halts_at_the_heartbeat` pins. The
//! composition therefore has to be stated at a module carrying the callee
//! models, which is what `ir_itd_module` already is.
//!
//! Read that way, the open increment is not "compose a segment" but
//! **generalize `ir_itd` off its pinned heap `ir_mem0`**, using this segment for
//! the tail. That is a different and better-shaped task than the sentence above
//! describes, and it leaves `ir_itd`'s two authored-model residuals untouched.
//!
//! # Why this is not vacuous, and why `ir_itd` is what settles that
//!
//! This lemma quantifies over `loc`, `ds`, `rest`, `v0`, `mem` and `na`, so on
//! its own it could be a true statement about a configuration the target never
//! reaches — the exact shape the vacuity firewall exists to refuse, since a
//! premise nothing satisfies passes every axiom census while proving nothing.
//!
//! `ir_itd` is what rules that out, and this is the reason the two chains are
//! kept side by side rather than one replacing the other:
//!
//! * `ir_itd_transports_the_inference_result` RUNS the target and passes
//!   THROUGH an instance of `ir_ite_smach` on its way to `ret` — so the seam
//!   configuration is reachable, witnessed concretely.
//! * `ir_it_transport_seg` shows that from that configuration the tail
//!   transports in general.
//!
//! Neither subsumes the other. The run pins reachability and names two models;
//! the seam pins generality and names none.
//!
//! Proof shape, borrowed wholesale from `eval_ir_slot_lemmas.rs`: a shape
//! witness restates the machine's own step with the stuck `ir_mem_lookup` /
//! `ir_mem_update` occurring SYNTACTICALLY, then nested `Eq.subst` + `Eq.symm`
//! rewrite them through `ir_mem_lookup_head` and `ir_mem_update_head`.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The frame's local bindings: `%2` is the Result slot pointer and `%29` is the
/// value `call 2` returned, over whatever else was already bound.
const SRC_ITE_LOC: &str = "def ir_ite_loc (a : Nat) (spv : IRScalar) (loc : IRList IRBinding) : IRList IRBinding := ir_bind_params (ir_nl2 ir_d2 ir_d29) (ir_vl2 (IRScalar.ptr_ a) (IRScalar.aggv spv)) loc";

/// The machine the instant `call 2` has returned: function 0, block 5, pc 1 —
/// the `store` is the next node.
const SRC_ITE_SMACH: &str = "def ir_ite_smach (a : Nat) (spv : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (v0 : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d5 ir_d1 (ir_ite_loc a spv loc) ds) rest) (IRList.cons IRMemSlot (IRMemSlot.mk a v0 Bool.true) mem) na";

/// The machine after the `br`, at block 3 pc 0, with the slot now holding the
/// transported value.
const SRC_ITE_BMACH: &str = "def ir_ite_bmach (a : Nat) (spv : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d3 ir_d0 (ir_ite_loc a spv loc) ds) rest) (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) na";

/// The store, with its liveness lookup SUSPENDED.
const SRC_ITE_AFTER_STORE_LOOKUP: &str = "def ir_ite_after_store_lookup (a : Nat) (spv : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (v0 : IRScalar) (mem : IRList IRMemSlot) (na : Nat) (o : IROption IRMemSlot) : IRConfig := ir_store_checked (ir_ite_smach a spv loc ds rest v0 mem na) a (IRScalar.aggv spv) o";

/// The store's commit, with its memory update SUSPENDED.
const SRC_ITE_AFTER_STORE_UPDATE: &str = "def ir_ite_after_store_update (a : Nat) (spv : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (v0 : IRScalar) (mem : IRList IRMemSlot) (na : Nat) (m2 : IRList IRMemSlot) : IRConfig := ir_advance (ir_set_mem (ir_ite_smach a spv loc ds rest v0 mem na) m2)";

/// The load, with its lookup SUSPENDED.
const SRC_ITE_AFTER_LOAD: &str = "def ir_ite_after_load (a : Nat) (spv : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) (o : IROption IRMemSlot) : IRConfig := ir_bind_result (ir_ite_bmach a spv loc ds rest mem na) (ir_nl1 ir_d5) (ir_load_slot o)";

/// Shape witness: the machine's own store step, with the lookup syntactic.
const SRC_ITE_STEP_STORE: &str = "def ir_ite_step_store (a : Nat) (spv : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (v0 : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_step ir_it_module (ir_ite_smach a spv loc ds rest v0 mem na)) (ir_ite_after_store_lookup a spv loc ds rest v0 mem na (ir_mem_lookup (IRList.cons IRMemSlot (IRMemSlot.mk a v0 Bool.true) mem) a)) := Eq.refl IRConfig (ir_ite_after_store_lookup a spv loc ds rest v0 mem na (ir_mem_lookup (IRList.cons IRMemSlot (IRMemSlot.mk a v0 Bool.true) mem) a))";

/// **THE SEAM LEMMA.** Four steps, no callee, arbitrary heap.
const SRC_ITE_SEG: &str = "def ir_it_transport_seg (a : Nat) (spv : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (v0 : IRScalar) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d4 ir_it_module (IRConfig.running (ir_ite_smach a spv loc ds rest v0 mem na))) (ir_ret_to ds rest (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) na (ir_vl1 (IRScalar.aggv spv))) := Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IRConfig (ir_steps ir_d3 ir_it_module (ir_ite_after_store_lookup a spv loc ds rest v0 mem na o)) (ir_ret_to ds rest (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) na (ir_vl1 (IRScalar.aggv spv)))) (IROption.some IRMemSlot (IRMemSlot.mk a v0 Bool.true)) (ir_mem_lookup (IRList.cons IRMemSlot (IRMemSlot.mk a v0 Bool.true) mem) a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup (IRList.cons IRMemSlot (IRMemSlot.mk a v0 Bool.true) mem) a) (IROption.some IRMemSlot (IRMemSlot.mk a v0 Bool.true)) (ir_mem_lookup_head a v0 Bool.true mem)) (Eq.subst (IRList IRMemSlot) (fun (m2 : (IRList IRMemSlot)) => Eq IRConfig (ir_steps ir_d3 ir_it_module (ir_ite_after_store_update a spv loc ds rest v0 mem na m2)) (ir_ret_to ds rest (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) na (ir_vl1 (IRScalar.aggv spv)))) (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) (ir_mem_update (IRList.cons IRMemSlot (IRMemSlot.mk a v0 Bool.true) mem) a (IRScalar.aggv spv)) (Eq.symm (IRList IRMemSlot) (ir_mem_update (IRList.cons IRMemSlot (IRMemSlot.mk a v0 Bool.true) mem) a (IRScalar.aggv spv)) (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) (ir_mem_update_head a v0 Bool.true mem (IRScalar.aggv spv))) (Eq.subst (IROption IRMemSlot) (fun (o : (IROption IRMemSlot)) => Eq IRConfig (ir_steps ir_d1 ir_it_module (ir_ite_after_load a spv loc ds rest mem na o)) (ir_ret_to ds rest (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) na (ir_vl1 (IRScalar.aggv spv)))) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true)) (ir_mem_lookup (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) a) (Eq.symm (IROption IRMemSlot) (ir_mem_lookup (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) a) (IROption.some IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true)) (ir_mem_lookup_head a (IRScalar.aggv spv) Bool.true mem)) (Eq.refl IRConfig (ir_ret_to ds rest (IRList.cons IRMemSlot (IRMemSlot.mk a (IRScalar.aggv spv) Bool.true) mem) na (ir_vl1 (IRScalar.aggv spv))))))";

/// The frame `call 1` returns into: function 0, block `b0`, pc 2 -- `ir_push`
/// advanced the caller's pc when it pushed, so the `br` is the next node.
const SRC_ITD_DFRAME: &str = "def ir_it_dframe (loc : IRList IRBinding) (ds : IRList Nat) : IRFrame := IRFrame.mk ir_d0 ir_d0 ir_d2 loc ds";

/// The heartbeat's OK answer: discriminant 0, and everything after it abstract.
const SRC_ITD_HBANS: &str = "def ir_it_hb_answer (sp : IRScalar) : IRScalar := IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ir_d0) sp)";

/// Where the dispatch lands: block `b5`, pc 0 -- sitting ON `call 2`.
const SRC_ITD_DEND: &str = "def ir_it_dispatch_end (sp : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) : IRMachine := IRMachine.mk (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d5 Nat.zero (IRList.cons IRBinding (IRBinding.mk ir_d4 (IRScalar.int_ ir_d0)) (IRList.cons IRBinding (IRBinding.mk ir_d3 (ir_it_hb_answer sp)) loc)) ds) rest) mem na";

/// **THE DISPATCH SEAM.** Three steps, no callee, arbitrary heap AND counter.
const SRC_ITD_DSEG: &str = "def ir_it_dispatch_seg (sp : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_steps ir_d3 ir_it_module (ir_ret_to (ir_nl1 ir_d3) (IRList.cons IRFrame (ir_it_dframe loc ds) rest) mem na (ir_vl1 (ir_it_hb_answer sp)))) (IRConfig.running (ir_it_dispatch_end sp loc ds rest mem na)) := Eq.refl IRConfig (IRConfig.running (ir_it_dispatch_end sp loc ds rest mem na))";

/// The seam ends exactly AT the callee boundary -- one more step attempts
/// `call 2`, which `ir_it_module` does not define.
const SRC_ITD_ATCALL: &str = "def ir_it_dispatch_ends_at_the_call (sp : IRScalar) (loc : IRList IRBinding) (ds : IRList Nat) (rest : IRList IRFrame) (mem : IRList IRMemSlot) (na : Nat) : Eq IRConfig (ir_step ir_it_module (ir_it_dispatch_end sp loc ds rest mem na)) (IRConfig.halted (IROutcome.stuck IRFault.no_func)) := Eq.refl IRConfig (IRConfig.halted (IROutcome.stuck IRFault.no_func))";

impl Specification {
    /// `ir_ite` — the transport tail as a seam, over the target alone.
    pub(super) fn add_eval_ir_ite(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_ITD_DFRAME, "ir_it_dframe: the frame `call 1` returns into -- function 0, block b0, pc 2. pc is 2 and not 1 because ir_push advances the CALLER's pc when it pushes, so the return resumes AFTER the call; the `br b1` terminator is the next node. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_HBANS, "ir_it_hb_answer: the heartbeat's ok answer -- discriminant 0 at slot 0, everything after it the abstract spine `sp`. The discriminant is pinned because it is what b1's extractfield reads and the switch selects on; the payload is quantified because nothing in the dispatch looks at it. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_DEND, "ir_it_dispatch_end: where the dispatch lands -- block b5, pc ZERO, sitting ON `call 2` and not through it. Both bindings the segment makes are visible: %3 the heartbeat's answer, %4 the tag it read. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_DSEG, "*** INFER_TYPE'S DISPATCH, OVER THE TARGET ALONE, AT AN ARBITRARY HEAP, WITH NO CALLEE NAMED. *** Three steps from the instant `call 1` returns -- br, extractfield, switch -- and the machine arrives at b5 pc 0, the ok branch, for every payload spine sp, every frame tail loc, every destination list ds, every caller stack rest, every heap mem and every allocation counter na. \n\nThis is the OTHER half of the body's ok path from ir_it_transport_seg, and it is strictly MORE general: this segment performs no ir_mem_lookup and no ir_mem_update, so the heap and counter are quantified outright rather than constrained to a live slot at the head. \n\nWhy it reduces with an abstract spine: the tag read is ir_vals_get at index ZERO, whose Nat.rec zero-minor returns the head and DISCARDS both induction hypotheses, so the neutral `sp` is never forced. The two binding lookups are head hits, so the abstract `loc` is never walked. \n\nThe discriminant is necessarily pinned -- it is the switch selector. Quantifying it would make the branch undecidable, which is the same boundary ir_itd states. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITD_ATCALL, "ir_it_dispatch_ends_at_the_call: one more step from the seam's endpoint attempts `call 2` and halts `stuck no_func`, because ir_it_module defines only the target. Registered so the seam's endpoint is pinned to the CALLEE BOUNDARY rather than to a block-and-pc a reader must trust: the segment stops exactly where the compositional rule would have to take over, which is the residual eval_ir_itc.rs names. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITE_LOC, "ir_ite_loc: the frame's locals at the seam -- %2 the Result slot pointer, %29 the value `call 2` returned, over an ARBITRARY tail `loc`. The tail can stay abstract because both names are concrete atoms, so `ir_nat_eqb` resolves each lookup before the walk ever reaches `loc`. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITE_SMACH, "ir_ite_smach: the machine the instant infer_type's `call 2` has returned -- function 0, block 5, pc 1, with the store as the next node. The Result slot is LIVE at the head of memory; that is this lemma's one hypothesis and it is a hypothesis on the SHAPE of mem rather than a proved fact, because between b0's alloca and this store sits the inference call, which in the seam framing is arbitrary and could allocate. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITE_BMACH, "ir_ite_bmach: the machine after the `br`, at block 3 pc 0, with the slot now holding the transported value. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITE_AFTER_STORE_LOOKUP, "ir_ite_after_store_lookup: the store with its liveness lookup SUSPENDED as a parameter. The suspension is the whole technique -- at an abstract address `ir_mem_lookup` is stuck at a neutral operand, so the shape witness below restates the machine's own step with the stuck call occurring syntactically and an Eq.subst rewrites it afterwards. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITE_AFTER_STORE_UPDATE, "ir_ite_after_store_update: the store's commit with its memory update SUSPENDED, for the same reason. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITE_AFTER_LOAD, "ir_ite_after_load: the load with its lookup SUSPENDED. No view rewrite is needed beside it: ir_mod_encs (IRModule.mk fs gs) is the empty table by computation, so ir_load_view is the identity definitionally here, where the lzd lane needs ir_load_view_agg because its module carries globals. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITE_STEP_STORE, "ir_ite_step_store: the shape witness -- the machine's own store step IS the suspended form, by computation. Registered separately from the segment so that a change to ir_exec's store arm stops THIS reducing, rather than silently changing what the segment lemma is about. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_ITE_SEG, "*** INFER_TYPE'S TRANSPORT TAIL, OVER THE TARGET ALONE, AT AN ARBITRARY HEAP, WITH NO CALLEE NAMED. *** Four steps from the instant `call 2` returns -- store, br, load, ret -- and what comes out is the value that went in, for every payload spine spv, every heap tail mem, every allocation counter na, every caller stack rest, every destination list ds, every other binding loc, and whatever v0 the slot held before. \\n\\nThis is ir_itd's content in the SEAM form. ir_itd proves transport by running the whole module, so its statement names two authored models and pins the heap to ir_mem0; here the module is ir_it_module -- infer_type and nothing else -- and every one of those is quantified away. The value is `IRScalar.aggv spv` rather than a bare variable because ir_load_value MATCHES on the scalar and is stuck at a neutral one; a head constructor is the weakest form that reduces and is the right one, since what infer_type transports is a Result aggregate. \\n\\nThe one assumption is the slot being LIVE at the head of memory -- the same one ir_slot_activation carries, for the same mechanical reason (a head lookup resolves through ir_nat_eqb a a = true; an unknown heap is stuck). \\n\\nWhat it does NOT do: it is a SEGMENT, not a run. Composing it into an end-to-end statement needs the dispatch seam and a composition step, and until those land ir_itd remains the only end-to-end execution of this target, with its two models as its stated residual. A4 is not claimed. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}
