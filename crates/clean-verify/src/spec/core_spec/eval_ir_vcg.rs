// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Link 4 W4: the obligation-checked symbolic-execution device, a SCRATCH stage.**
//!
//! CrystalVC's M0 second falsifier
//! (`designs/2026-09-30-link4-crystalvc-plan.md` §6, M2's entry). The device decides
//! a straight-line segment of an EvalIR body by EVALUATION: an untrusted engine runs
//! the real `ir_step` on placeholders and reifies each step, and ONE list equation per
//! segment, proved by `Eq.refl`, carries the segment
//! (`ir_vcg_check` / `ir_vcg_check_call`). Memory steps go through proved lemmas
//! (`ir_vcg_lookup_sound`, `ir_vcg_update_sound`). Soundness is `ir_vcg_run_sound`, read
//! through `ir_vcg_check_sound`. Calls compose with the step-indexed contract device
//! (`ir_ctr_*`) through generic glue (`ir_vcg_seg_call1/2`, `ir_vcg_seg_ret`).
//!
//! `vcg/lzd.clean` is minted by `reports/crystal-lane/2026-09-30-link4-m0/w4/gen_vcg_lzd.py`.
//! It RE-DERIVES `ir_lzd_ctr` with no lemma about the body, as `ir_vcg_lzd_ctr`, and the two
//! `ir_ctr_weaken` cross-checks against the landed one.
//!
//! `vcg/device.clean` is in five sections. Section 2, the MEMORY INTERFACE, is the part a
//! byte-level memory model (D20, ByteV1) replaces; the record lists exactly what changes.
//!
//! This module is in NO bundle. Its tests register it on top of the EvalIR bundle (device plus
//! per-case contracts) and on top of the full spec (the contract table, which needs `IRLzdIn`).
//! It is therefore not in the Lean export either. Lean's elaborator exhausts recursion depth
//! on an `Eq.refl` certificate, so leancross needs kernel-only emission first (plan M2). The
//! record re-checks every declaration in Lean kernel-only.
//!
//! **W4b** (`reports/crystal-lane/2026-10-07-link4-m0/w4b/`) supersedes the W4 device for
//! registration: `vcg/w4b_device.clean` takes the engine OUT of the kernel (the generator
//! materialises every intermediate state as a delta trace, `ir_vcg_expand`, and one `Eq.refl`
//! per segment checks each step's transition against the real step), routes every step's
//! function fetch through a per-body function table proved once against the module
//! (`ir_vcg_stepT`, `ir_vcg_step_ft`), and discharges every call and return boundary with ONE
//! generic composed lemma (`ir_vcg_callo` and its result-shape wrappers, `ir_vcg_rsafe`,
//! `ir_vcg_xretT`). Two bodies use it: `ir_lzd` (`vcg/w4b_lzd.clean`, re-deriving
//! `ir_lzd_ctr`) and `EquivManager::is_zfc_set_equiv` (`vcg/w4b_zse_module.clean` and
//! `vcg/w4b_zse.clean`, a safety contract with its callee's contract as a premise). The W4 sources
//! are kept for the W4 record's Lean re-check (`w4/lean/check.sh`); no test registers them, because
//! both devices define the same `ir_vcg_*` names. The retained W4 source is
//! explicitly the pre-Release32 syntax epoch; it is not registered against the
//! current33 family or claimed rechecked by current W4b tests.

use super::{SpecError, Specification};

/// The device: values, the memory interface, machine and steps, check and contract glue, engine.
pub(crate) const VCG_DEVICE: &str = include_str!("vcg/device.clean");
/// `ir_lzd`'s per-function glue, minted (see the module docs).
pub(crate) const VCG_LZD: &str = include_str!("vcg/lzd.clean");
/// The comment block in `VCG_LZD` that opens the part needing the full spec.
pub(crate) const VCG_TABLE_MARKER: &str = "-- == TABLE:";
/// W4b: the device (see the module docs).
pub(crate) const W4B_DEVICE: &str = include_str!("vcg/w4b_device.clean");
/// W4b: `ir_lzd`'s per-function glue, minted; its table follows `VCG_TABLE_MARKER`.
pub(crate) const W4B_LZD: &str = include_str!("vcg/w4b_lzd.clean");
/// W4b: the second body's module (the body plus a stub callee), minted.
pub(crate) const W4B_ZSE_MODULE: &str = include_str!("vcg/w4b_zse_module.clean");
/// W4b: the second body's per-function glue, minted.
pub(crate) const W4B_ZSE: &str = include_str!("vcg/w4b_zse.clean");

/// One declaration of a `.clean` source: blocks separated by a blank line; a block opening
/// with `--` is a comment. An `inductive` keeps its constructor lines; any other declaration
/// is joined onto one line, and `kdef` (Lean's kernel-only mark) is registered as `def`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct VcgDecl {
    pub(crate) name: String,
    pub(crate) inductive: bool,
    pub(crate) source: String,
}

/// Parse a `.clean` source into declarations, in order. With `until` set, stop at the first
/// comment block that starts with it.
pub(crate) fn vcg_decls(text: &str, until: Option<&str>) -> Vec<VcgDecl> {
    let mut out = Vec::new();
    for raw in text.split("\n\n") {
        let block = raw.trim();
        if block.is_empty() {
            continue;
        }
        if block.starts_with("--") {
            if until.is_some_and(|marker| block.starts_with(marker)) {
                break;
            }
            continue;
        }
        let inductive = block.starts_with("inductive ");
        let source = if inductive {
            block.to_string()
        } else {
            let one = block.split_whitespace().collect::<Vec<_>>().join(" ");
            match one.strip_prefix("kdef ") {
                Some(rest) => format!("def {rest}"),
                None => one,
            }
        };
        let name = source
            .split_whitespace()
            .nth(1)
            .unwrap_or_default()
            .to_string();
        out.push(VcgDecl {
            name,
            inductive,
            source,
        });
    }
    out
}

/// The declarations of `VCG_LZD` after the table marker's comment block.
pub(crate) fn vcg_lzd_table() -> Vec<VcgDecl> {
    vcg_table(VCG_LZD)
}

/// The declarations of `text` after the table marker's comment block.
pub(crate) fn vcg_table(text: &str) -> Vec<VcgDecl> {
    text.split_once(VCG_TABLE_MARKER)
        .and_then(|(_, rest)| rest.split_once("\n\n"))
        .map(|(_, table)| vcg_decls(table, None))
        .unwrap_or_default()
}

impl Specification {
    /// Register `decls` in order, returning each declaration's registration seconds.
    pub(crate) fn add_eval_ir_vcg_decls(
        &mut self,
        decls: &[VcgDecl],
    ) -> Result<Vec<(String, f64)>, SpecError> {
        let mut times = Vec::with_capacity(decls.len());
        for decl in decls {
            let t = std::time::Instant::now();
            if decl.inductive {
                self.add_inductive(&decl.source, "link 4 W4 device (scratch)")?;
            } else {
                self.add_recursive_def(&decl.source, "link 4 W4 device (scratch)")?;
            }
            times.push((decl.name.clone(), t.elapsed().as_secs_f64()));
        }
        Ok(times)
    }
}

#[cfg(test)]
#[path = "eval_ir_vcg_tests.rs"]
mod tests;
