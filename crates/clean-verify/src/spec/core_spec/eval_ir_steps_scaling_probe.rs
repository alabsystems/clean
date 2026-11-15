// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How far does `ir_steps` REDUCE? — the measurement link 4's `hc2` route needs.
//!
//! The backlog prices `hc2` (`infer_type_fast`, 113 functions / 7,379 instructions) at
//! "~131 spec chars per instruction, i.e. ~0.97M chars ... so it can be discharged by a
//! standalone run". That figure prices the REGISTRATION. It says nothing about the
//! REDUCTION, and the two are different costs.
//!
//! The in-tree evidence about reduction points the other way: the largest `ir_steps`
//! literal proved anywhere is `ir_d40`, and forty steps already forced an 8x heartbeat
//! raise (`emit.rs` records the ceiling "was 4,000,000 and `gate::leancross` was RED
//! under it with two `(deterministic) timeout at whnf` diagnostics plus four cascades").
//!
//! THE PROBE. A module does not need 7,379 instructions to make `ir_steps` do N
//! dispatches — it needs a step that returns to its own starting configuration. One
//! block whose only instruction is `br` to itself does exactly that: the frame's block
//! and pc both return to zero and the bindings are untouched, so
//!
//!     ir_steps N loop_module loop_cfg  ==  loop_cfg     for every N
//!
//! and the checker has to perform N full `ir_step` dispatches to see it. That isolates
//! the per-step cost from module size, which is the variable the real `hc2` adds on top.
//!
//! WHAT IT CAN AND CANNOT SETTLE. A LOWER bound. `ir_step` walks the module's function
//! list and the function's block list on every step, so per-step cost grows with module
//! size, and this module is the smallest one that runs. If the minimal case already
//! degrades by a few hundred steps, `hc2`-by-computation is settled negative and no
//! 0.97M-char registration need be written. If it stays flat into the thousands, then
//! module size is the dominant term and THAT is the thing to measure next — a different
//! and much more useful question than the one the char-count answers.
//!
//! SCRATCH and unwired: nothing gates on it, and a failure here is a measurement.

use crate::spec::Specification;

impl Specification {
    /// The loop module, and the step-count ladder over it.
    #[cfg(test)]
    pub(super) fn eval_ir_steps_scaling_sources() -> Vec<(String, String)> {
        let mut v: Vec<(String, String)> = vec![
            (
                "ir_sc_blk".to_string(),
                // One block, id 0, no params, one node: `br 0 []`, no results.
                "def ir_sc_blk : IRBlock := IRBlock.mk ir_d0 ir_nl0 \
                 (ir_bd1 (IRNode.mk (IRInst.br ir_d0 ir_nl0) ir_nl0))"
                    .to_string(),
            ),
            (
                "ir_sc_func".to_string(),
                "def ir_sc_func : IRFunc := IRFunc.mk ir_d0 ir_nl0 ir_d0 \
                 (ir_blk ir_sc_blk ir_blk0)"
                    .to_string(),
            ),
            (
                "ir_sc_module".to_string(),
                "def ir_sc_module : IRModule := IRModule.mk \
                 (IRList.cons IRFunc ir_sc_func (IRList.nil IRFunc)) (IRList.nil IRGlobal)"
                    .to_string(),
            ),
            (
                "ir_sc_cfg".to_string(),
                "def ir_sc_cfg : IRConfig := IRConfig.running (IRMachine.mk \
                 (IRList.cons IRFrame (IRFrame.mk ir_d0 ir_d0 ir_d0 (IRList.nil IRBinding) ir_nl0) \
                 (IRList.nil IRFrame)) (IRList.nil IRMemSlot) ir_d0)"
                    .to_string(),
            ),
        ];
        // STEP LADDER. Numerals by DOUBLING from `ir_d99` rather than a `Nat.succ` tower:
        // the tower's own term size would grow with the step count and confound the very
        // thing being measured. Registered numerals are 0-31, 33-63, 66-99 -- 32, 64 and 65
        // are absent, and picking one reads as a reduction failure when it is an elaboration
        // one, which is exactly what the first run of this probe did.
        let mut rungs: Vec<(usize, String)> = vec![
            (1, "ir_d1".into()),
            (2, "ir_d2".into()),
            (4, "ir_d4".into()),
            (8, "ir_d8".into()),
            (16, "ir_d16".into()),
            (31, "ir_d31".into()),
            (63, "ir_d63".into()),
            (99, "ir_d99".into()),
        ];
        let mut cur = ("ir_sc_n99".to_string(), 99usize);
        v.push((
            "ir_sc_n99".to_string(),
            "def ir_sc_n99 : Nat := ir_d99".to_string(),
        ));
        for _ in 0..6 {
            let (name, n) = cur.clone();
            let n2 = n * 2;
            let nm2 = format!("ir_sc_n{n2}");
            v.push((
                nm2.clone(),
                format!("def {nm2} : Nat := Nat.add {name} {name}"),
            ));
            rungs.push((n2, nm2.clone()));
            cur = (nm2, n2);
        }
        v.push((
            "ir_sc_n4752".to_string(),
            "def ir_sc_n4752 : Nat := Nat.add ir_sc_n3168 ir_sc_n1584".to_string(),
        ));
        rungs.push((4752, "ir_sc_n4752".to_string()));
        // BRACKET THE WALL FINELY (v4). v3 put it between 4,752 (OK, 20.1 s) and 6,336
        // (REFUSED after 51 s with a kernel `Type mismatch`). These four rungs quarter that
        // interval, so the wall is located to ~400 steps rather than ~1,600, and the full
        // error text is captured rather than truncated -- a refusal WITH A SHAPE can be read
        // and possibly lifted, which is the whole reason it matters that this is not a timeout.
        for (n, expr) in [
            (5148usize, "Nat.add ir_sc_n4752 ir_sc_n396"),
            (5544, "Nat.add ir_sc_n4752 ir_sc_n792"),
            (5940, "Nat.add ir_sc_n5148 ir_sc_n792"),
        ] {
            v.push((
                format!("ir_sc_n{n}"),
                format!("def ir_sc_n{n} : Nat := {expr}"),
            ));
            rungs.push((n, format!("ir_sc_n{n}")));
        }
        // AND DOES THE WALL MOVE WITH MODULE SIZE? Every K rung below runs at 99 steps, so
        // v3 measured per-step COST against K and said nothing about where K=113 stops. If
        // the wall is about accumulated term size rather than step count alone, it arrives
        // EARLIER at a larger module -- and `hc2`'s module is the large one.
        // BRACKET the wall. v2 was linear through 3,168 steps (13.3 s) and then REFUSED at
        // 6,336 with a kernel "Type mismatch" after 49.9 s -- a refusal, not a timeout, so the
        // interesting question is WHERE between them it changes character and whether the
        // failure tracks the step count or the `Nat.add` numeral. The numeral is not the
        // suspect: `ir_sc_n6336` itself elaborated in 0.001 s.
        // 6,336 already exists from the doubling loop above -- pushing it again registers a
        // DUPLICATE, which the kernel refuses and which then reads as a probe failure. Reuse it.
        rungs.push((6336, "ir_sc_n6336".to_string()));
        for (n, lit) in &rungs {
            v.push((
                format!("ir_sc_run_{n}"),
                format!(
                    "def ir_sc_run_{n} : Eq IRConfig (ir_steps {lit} ir_sc_module ir_sc_cfg) \
                     ir_sc_cfg := Eq.refl IRConfig ir_sc_cfg"
                ),
            ));
        }
        // MODULE-SIZE LADDER, which is the axis `hc2` actually adds. `ir_step` resolves the
        // running frame's function with `ir_func_find`, a LIST WALK, on every step -- so the
        // per-step cost is a function of where the entered function sits, not just of how
        // many steps run. The padding functions carry ids 1..K and NO blocks (never entered)
        // and the entered id-0 function is placed LAST, so each step walks all K.
        for k in [8usize, 32, 113] {
            let mut fs = "(IRList.cons IRFunc ir_sc_func (IRList.nil IRFunc))".to_string();
            for i in (1..=k).rev() {
                // Ids cycle over 1..=31, which ARE registered. 32, 64 and 65 are not, and
                // reaching for one is how v1 and v2 both produced an "Unknown identifier"
                // that reads like a measurement and is not one. Duplicates are harmless:
                // `ir_func_find` returns the FIRST match and the entered id-0 function is
                // last, so every step still walks all K.
                let pad = format!("(IRFunc.mk ir_d{} ir_nl0 ir_d0 ir_blk0)", (i % 31) + 1);
                fs = format!("(IRList.cons IRFunc {pad} {fs})");
            }
            v.push((
                format!("ir_sc_mod_k{k}"),
                format!("def ir_sc_mod_k{k} : IRModule := IRModule.mk {fs} (IRList.nil IRGlobal)"),
            ));
            v.push((
                format!("ir_sc_k{k}_run99"),
                format!(
                    "def ir_sc_k{k}_run99 : Eq IRConfig (ir_steps ir_d99 ir_sc_mod_k{k} ir_sc_cfg) \
                     ir_sc_cfg := Eq.refl IRConfig ir_sc_cfg"
                ),
            ));
            if k == 113 {
                for (n, lit) in [
                    (396usize, "ir_sc_n396"),
                    (792, "ir_sc_n792"),
                    (1584, "ir_sc_n1584"),
                ] {
                    v.push((
                        format!("ir_sc_k113_run{n}"),
                        format!(
                            "def ir_sc_k113_run{n} : Eq IRConfig \
                             (ir_steps {lit} ir_sc_mod_k113 ir_sc_cfg) ir_sc_cfg := \
                             Eq.refl IRConfig ir_sc_cfg"
                        ),
                    ));
                }
            }
        }
        v
    }
}

#[cfg(test)]
#[path = "eval_ir_steps_scaling_probe_tests.rs"]
mod tests;
