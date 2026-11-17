// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RM4 (Trust `docs/plans/2026-10-15-proven-core.md` §5, milestone RM4): SemR,
//! trust-ir level R's one semantics, kernel-checked by Clean THROUGH the reference
//! entry, every closure ⊆ Ax0.
//!
//! The fixture family `tests/fixtures/lean/v4.30.0-rc2/semr/` holds trust-ir's
//! `lean/semr/SemR.lean`, `MiniRust.lean`, `SemRMiniRust.lean`, `SemRMemory.lean`
//! and `ClosureConstruction.lean` byte for byte
//! ([`SEMR_SHA256`], [`MINIRUST_WRAPPER_SHA256`], [`SEMR_MINIRUST_SHA256`],
//! [`SEMR_MEMORY_SHA256`] and [`CLOSURE_CONSTRUCTION_SHA256`] pin
//! them; trust-ir pins the same digests of its own copies, so the copies cannot
//! drift apart without a test going red) and `SemRCheck.lean`, which imports
//! them. SemR is level R's syntax, the binary decoder, the operator layer, the
//! small-step relation `Step` (one rule per instruction, never mentioning the
//! executable) and the run relation `Exec` over it, with `step_sound` and
//! `step_complete` tying the executable `stepCore` to the relation; `MiniRust.lean`
//! is Trust's specr translator output (the `trust_sem` family's two files, in a
//! `noncomputable section`: `semr_minirust_copy_is_the_trust_sem_slice`), and
//! `SemRMiniRust.lean` proves SemR's operator layer is MiniRust's generated
//! operators for every integer type (`intBin_minirust`, `intUn_minirust`,
//! `icmp_minirust`, `ovf_minirust`). No `native_decide` and no `partial def`;
//! trust-ir's `semr_*` differential holds the executable to the reference
//! interpreter. Here:
//!
//! * all thirteen modules are compiled by the pinned `lean -o` (Lean's kernel checks
//!   them), and every constant in the cone of the checked theorems — SemR's
//!   decoder and semantics, the pinned `Init` they use — is admitted from empty
//!   through `ReferenceKernel` (`reference_base_closed`, R143's Ax0 fence among
//!   its gates);
//! * each theorem's closure, read from the entry's own environment, is what Lean
//!   4.30's `#print axioms` prints for it ([`EXPECTED`]) and ⊆ Ax0, and no
//!   cone reaches `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat` or
//!   `Lean.trustCompiler`;
//! * `step_sound`, `step_complete`, `step_det`, `run_sound`, `run_complete` and
//!   `exec_det`, the four operator lemmas, the kernel-evaluated runs and decodes
//!   of a real trust-ir blob (`SemRCheck.sub_*`, `blob_decodes`, the three refused
//!   corruptions) and two operator instances (`i8_min_div_neg_one`,
//!   `u8_sub_wraps`) are admitted under their own names;
//! * negative controls on the same entry, each beside an accepted control: the
//!   proof of `sub_5_3` offered for the wrong result, `blob_decodes`'s proof
//!   offered for the blob with a trailing byte, `run_sound`'s proof offered
//!   for `ForgedRunSound` (every run out of fuel), `step_complete`'s proof
//!   offered for `ForgedStep` (every state steps out of fuel) and
//!   `i8_min_div_neg_one`'s proof offered for `ForgedSdiv` (MiniRust's `i8`
//!   `MIN / -1` is a value), whose negations `forged_run_sound_fails`,
//!   `forged_step_fails` and `forged_sdiv_fails` are admitted.
//!
//! The audit covers EVERY constant all thirteen modules declare (their `.olean`'s
//! own constant list, so a `_root_` declaration is in it too), not only the
//! cones of [`EXPECTED`]: each is admitted through the entry, is neither an
//! axiom nor an opaque constant (a `partial def` is one, beside its unsafe
//! implementation, which the replay refuses), and has a closure ⊆ Ax0 that
//! reaches none of the native-evaluation or sorry constants (at v4.30 a
//! `native_decide` proof cites its own auxiliary axiom, so the closure check
//! catches it). The source tripwire stays for what the kernel cannot see
//! (`implemented_by`, `extern`), and lexes strings, characters and comments
//! so a literal cannot hide code from it. Both layers have negative controls
//! over the `semr_forged` family, which smuggles a `native_decide` theorem
//! and a `partial def` behind a `'"'` character literal.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};

use clean_kernel::env::{ConstantKind, Declaration, Environment};
use clean_kernel::expr::{Expr, ExprKind, UsedConstants};
use clean_kernel::name::Name;
use clean_kernel::{ReferenceKernel, ReferenceRefusal, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, load_modules_with_deps, parse_module, reference_base_closed,
    DefinitionSafety,
};
use sha2::{Digest, Sha256};

#[path = "support/lean_axiom_census.rs"]
mod lean_axiom_census;
#[path = "support/lean_tripwire.rs"]
mod lean_tripwire;
use lean_tripwire::{banned_words, lean_code_only};

const PINNED: &str = "v4.30.0-rc2";
const FAMILY: &str = "semr";
const MODULE: &str = "SemRCheck";

/// SHA-256 of `SemR.lean`, the same constant trust-ir's
/// `crates/trust-ir-conformance/tests/lean_exec_differential.rs`
/// (`SEMR_SOURCE_SHA256`) pins for `lean/semr/SemR.lean`.
const SEMR_SHA256: &str = "91eba0576bb0fb6d8d8120b5227155bf660e6a336b0d3b68c2666195557329e0";

/// SHA-256 of `MiniRust.lean` and `SemRMiniRust.lean`, the constants trust-ir's
/// `lean_exec_differential.rs` (`MINIRUST_WRAPPER_SHA256`, `SEMR_MINIRUST_SHA256`)
/// pins for `lean/semr/`.
const MINIRUST_WRAPPER_SHA256: &str =
    "0de8e8aa1c30f277e4a2bca00b44696d5cf803fffc081767e067d5f713ecef51";
const SEMR_MINIRUST_SHA256: &str =
    "edc17ec135c79a02e2e3a36e51c03c3c56bbec5adec8371c57087e9ef29e965c";
const SEMR_MEMORY_SHA256: &str = "76ae6a87c7140e2afde71a18bb5a7e7597b58370c0af48989e5ee59cf8992577";
const CLOSURE_CONSTRUCTION_SHA256: &str =
    "d65f33468b3d7d5732e2fd683f8c8240a3cd1530d0df8ff4efd4f3bac7297468";
const METADATA_CHECK_SHA256: &str =
    "88889e327613a36e928757e604ac6474f184bb13ba908bc7c58586fd036c1939";

/// The fixture's explicit source revision, independently of the workspace's
/// compiled dependency pin. An unpublished candidate grants no landing credit.
const SEMR_SOURCE_REVISION: &str = "90619767a1d9b0c877702a651515da5073d68668";
const MODEL_MODULES: [&str; 13] = [
    "SemR",
    "SemRUnsignedSelect",
    "MiniRust",
    "SemRMiniRust",
    "SemRMemory",
    "ClosureConstruction",
    "ClosureAxiomAudit",
    "U64Addition",
    "U64AdditionAudit",
    "U64ScalarProfile",
    "U64AdditionConsumer",
    "MetadataCheck",
    MODULE,
];

/// The fixture files trust-ir owns (`lean/semr/<file>`), each with its pin.
const TRUST_IR_COPIES: [(&str, &str); 9] = [
    ("SemR.lean", SEMR_SHA256),
    ("MiniRust.lean", MINIRUST_WRAPPER_SHA256),
    ("SemRMiniRust.lean", SEMR_MINIRUST_SHA256),
    ("SemRMemory.lean", SEMR_MEMORY_SHA256),
    ("ClosureConstruction.lean", CLOSURE_CONSTRUCTION_SHA256),
    ("MetadataCheck.lean", METADATA_CHECK_SHA256),
    (
        "ClosureAxiomAudit.lean",
        "9b4274dcba8e1e4c60a26d5b720eab973eb972c44b6c8fb536e9b2851a687c35",
    ),
    (
        "U64Addition.lean",
        "f504dcc8798ebb49b733f0212b0b7fb4b231d816d942cdd7fa6b6a7c3d605965",
    ),
    (
        "U64AdditionAudit.lean",
        "565182e2b7edce999318672aab630cb6aa952bce5c73249dbc0a85d892c561a3",
    ),
];

/// Each checked theorem and the closure Lean 4.30's `#print axioms` reports.
const EXPECTED: &[(&str, &[&str])] = &[
    // Canonical scalar subjects and the generic decoded profile are independently rechecked.
    ("SemRU64Addition.original_decodes", &["propext"]),
    ("SemRU64Addition.current_decodes", &["propext"]),
    (
        "SemRU64Addition.run_exact",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64Addition.original_return",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64Addition.no_body_violation",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64Addition.original_no_body_violation",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64Addition.minirust_add",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemRU64ScalarProfile.classify_exact", &["propext"]),
    (
        "SemRU64ScalarProfile.decode_profile",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64ScalarProfile.decoded_module",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64ScalarProfile.start_exact",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64ScalarProfile.run_exact",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64ScalarProfile.returns",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRU64ScalarProfile.no_bad",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    // Published quoted capture-projection roots; exact Lean axiom closures.
    (
        "SemR.evalExtract_closure_of_checked",
        &["Quot.sound", "propext"],
    ),
    ("SemR.extractClosureStep_exact", &["Quot.sound", "propext"]),
    ("SemR.extractClosure_step_exact", &["Quot.sound", "propext"]),
    (
        "SemR.extractClosure_step_preserves_memory",
        &["Quot.sound", "propext"],
    ),
    (
        "SemR.closure_direct_pointer_return",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.closure_adapter_pointer_return",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.closure_direct_pointer_return_any_memory",
        &["propext"],
    ),
    ("SemR.closure_extract_null", &["propext"]),
    ("SemR.closure_extract_wrong_result_type", &["propext"]),
    ("SemR.closure_extract_wrong_value_kind", &["propext"]),
    ("SemR.closure_extract_target_is_not_a_field", &["propext"]),
    (
        "SemR.closure_extract_wrong_nominal_argument",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.closure_extract_unwritten", &["propext"]),
    ("SemR.closure_extract_poison_aggregate", &["propext"]),
    ("SemR.closure_extract_does_not_invoke_target", &["propext"]),
    (
        "SemR.closure_extract_scalar_is_not_an_environment",
        &["propext"],
    ),
    (
        "SemR.closure_extract_nominal_capture_type_is_exact",
        &["propext"],
    ),
    (
        "SemR.closure_direct_pointer_wrong_offset_refuted",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    // Exact published quoted-construction roots, including the v63 refusal.
    ("SemR.intTy_code_injective", &["propext"]),
    ("SemR.ty_beq_exact", &["Quot.sound", "propext"]),
    ("SemR.tyListEq_exact", &["Quot.sound", "propext"]),
    ("SemR.makesClosure_contract", &["Quot.sound", "propext"]),
    ("SemR.bindResults_success", &[]),
    ("SemR.makeClosureOn_success", &["propext"]),
    ("SemR.makeClosureStep_success", &["propext"]),
    ("SemR.makeClosure_step_success", &["propext"]),
    ("SemR.makeClosure_step_preserves_memory", &["propext"]),
    (
        "SemR.makeClosure_step_exact_result",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.construction_module_entry",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.construction_module_return",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.construction_pointer_exact", &["propext"]),
    ("SemR.construction_pointer_relational", &["propext"]),
    ("SemR.construction_pointer_return", &["propext"]),
    ("SemR.construction_nominal_identity", &["propext"]),
    ("SemR.construction_missing_definition", &["propext"]),
    ("SemR.construction_missing_apparent", &["propext"]),
    ("SemR.construction_missing_target", &["propext"]),
    ("SemR.construction_missing_physical", &["propext"]),
    ("SemR.construction_bad_prefix", &["propext"]),
    ("SemR.construction_bad_return", &["propext"]),
    ("SemR.construction_vararg_apparent", &["propext"]),
    ("SemR.construction_vararg_physical", &["propext"]),
    ("SemR.construction_wrong_capture_type", &["propext"]),
    ("SemR.construction_wrong_capture_arity", &["propext"]),
    ("SemR.construction_poison_capture", &["propext"]),
    ("SemR.construction_missing_operand", &["propext"]),
    ("SemR.construction_wrong_result_arity", &["propext"]),
    ("SemR.construction_instruction_v63_refused", &["propext"]),
    ("SemR.construction_wire_future_refused", &["propext"]),
    ("SemR.construction_wire_v64_payload_required", &["propext"]),
    ("SemR.construction_wire_v65_payload_required", &["propext"]),
    (
        "SemR.single_inhabited_v65_remains_explicitly_unsupported",
        &["propext"],
    ),
    (
        "SemR.single_inhabited_tag_is_malformed_under_old_header",
        &["propext"],
    ),
    (
        "SemR.empty_nominal_does_not_fabricate_a_semr_tag",
        &["propext"],
    ),
    ("SemR.makesClosure_complete", &["propext"]),
    ("SemR.makesClosure_sound", &["propext"]),
    ("SemR.makeClosure_sound", &["propext"]),
    ("SemRCheck.forged_closure_wire_fails", &["propext"]),
    ("SemR.step_sound", &["propext"]),
    ("SemR.step_complete", &["propext"]),
    ("SemR.step_det", &["propext"]),
    ("SemR.run_sound", &["propext"]),
    ("SemR.run_complete", &["propext"]),
    ("SemR.exec_det", &["propext"]),
    (
        "SemR.intBin_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.intUn_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.icmp_minirust", &["Quot.sound", "propext"]),
    (
        "SemR.ovf_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.ctpop_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.bitwise_resid",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.evalBinop_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.evalUnop_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.evalIcmp_minirust", &["Quot.sound", "propext"]),
    (
        "SemR.evalOverflow_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.icmp_bool_minirust", &["propext"]),
    ("SemR.mr_ptr_size", &[]),
    ("SemR.mr_usize", &[]),
    (
        "SemRCheck.sub_5_3",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.sub_3_5",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.sub_min_1",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemRCheck.blob_decodes", &["propext"]),
    ("SemRCheck.bad_magic_refused", &["propext"]),
    ("SemRCheck.trailing_byte_refused", &["propext"]),
    ("SemRCheck.truncated_refused", &["propext"]),
    ("SemRCheck.forged_run_sound_fails", &["propext"]),
    ("SemRCheck.forged_step_fails", &["propext"]),
    (
        "SemRCheck.i8_min_div_neg_one",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.u8_sub_wraps",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.forged_sdiv_fails",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.i8_and_signed",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.forged_and_signed_fails",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.i8_ctpop_neg_one",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.forged_ctpop_fails",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.pow_bytes_target", &[]),
    (
        "SemR.decodeVal_encodeVal_int_target",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.readOut_after_store_target",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.step_load_after_dealloc", &["propext"]),
    ("SemR.step_store_after_dealloc", &["propext"]),
    ("SemR.alloc_fresh", &["Quot.sound", "propext"]),
    (
        "SemR.encode_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.decode_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.accessAlloc_minirust", &["Quot.sound", "propext"]),
    ("SemRCheck.usize32_footprint", &["propext"]),
    ("SemRCheck.usize64_footprint", &["propext"]),
    ("SemRCheck.u64_on32_footprint", &["propext"]),
    ("SemRCheck.usize32_image", &["propext"]),
    ("SemRCheck.wrong_usize32_image_refused", &["propext"]),
    ("SemRCheck.wrong_usize32_footprint_refused", &["propext"]),
    ("SemRCheck.unit_u64_count32", &["propext"]),
    ("SemRCheck.unit_u64_index32", &["propext"]),
    ("SemRCheck.last_byte32_allocates", &[]),
    ("SemRCheck.past_last_byte32_refuses", &[]),
    ("SemRCheck.same_allocation64_fits", &[]),
    ("SemRCheck.wrong_allocation32_refused", &[]),
    (
        "SemRCheck.usize32_store_load",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    // Main's RM4c memory laws and native forgery controls, beside the target-width laws.
    ("SemR.readBytes_writeBytes", &["Quot.sound", "propext"]),
    (
        "SemR.readBytes_writeBytes_disjoint",
        &["Quot.sound", "propext"],
    ),
    (
        "SemR.fromLE_leBytes",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.decodeVal_encodeVal_int",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.readOut_after_store",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.accessAt_dead", &["propext"]),
    ("SemR.accessAt_oob", &["Quot.sound", "propext"]),
    ("SemR.accessAt_ok", &["Quot.sound", "propext"]),
    ("SemR.step_double_dealloc", &["propext"]),
    (
        "SemR.load_decode_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.leBytes_fromLE", &["Quot.sound", "propext"]),
    (
        "SemR.isPow2_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemR.checkAlign_minirust",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemR.aligned_minirust", &["Quot.sound", "propext"]),
    ("SemR.check_ptr_eq", &["Quot.sound", "propext"]),
    ("SemR.alignUp_aligned", &["Quot.sound", "propext"]),
    ("SemR.below_empty", &[]),
    (
        "SemR.below_setNth",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemRCheck.mem_blob_decodes", &["propext"]),
    (
        "SemRCheck.mem_roundtrip",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.mem_load_after_dealloc",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.mem_past_the_slot",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.mem_misaligned",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.mem_byte_one",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.forged_use_after_free_fails",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.forged_big_endian_fails",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.u32_encode",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.forged_encode_fails",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.i32_decode",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    (
        "SemRCheck.forged_decode_fails",
        &["Classical.choice", "Quot.sound", "propext"],
    ),
    ("SemRCheck.misaligned_1025", &["Quot.sound", "propext"]),
    ("SemRCheck.forged_aligned_fails", &["Quot.sound", "propext"]),
    ("SemRCheck.dead_slot_check_ptr", &["Quot.sound", "propext"]),
    (
        "SemRCheck.forged_dead_access_fails",
        &["Quot.sound", "propext"],
    ),
];

const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];
/// The quotient formers: part of the theory, not axioms (Ax0's definition).
const QUOT_FORMERS: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(name: &str) -> Expr {
    Expr::const_(n(name), vec![])
}

fn pinned_lib() -> PathBuf {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this fixture is compiled by {PINNED}; the workspace pin moved"
    );
    clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (RM4 reads lean-{PINNED})"))
}

/// Every constant `root` reaches through types, values, inductive families,
/// constructors and recursors, by name.
fn reach(env: &Environment, root: &Name) -> HashSet<Name> {
    let mut seen: HashSet<Name> = HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(x) = stack.pop() {
        if !seen.insert(x.clone()) {
            continue;
        }
        let mut used = HashSet::new();
        let walk = |e: &Expr, used: &mut HashSet<Name>| {
            e.used_constants_dag(UsedConstants::WithProjectionStructures, used);
        };
        if let Some(c) = env.get_const(&x) {
            walk(&c.type_, &mut used);
            if let Some(v) = &c.value {
                walk(v, &mut used);
            }
        }
        if let Some(i) = env.get_inductive(&x) {
            walk(&i.type_, &mut used);
            used.extend(i.constructor_names.iter().cloned());
            used.extend(i.all_names.iter().cloned());
        }
        if let Some(c) = env.get_constructor(&x) {
            walk(&c.type_, &mut used);
            used.insert(c.inductive_name.clone());
        }
        if let Some(r) = env.get_recursor(&x) {
            walk(&r.type_, &mut used);
            used.insert(r.inductive_name.clone());
        }
        stack.extend(used.into_iter().filter(|u| !seen.contains(u)));
    }
    seen
}

/// The axioms `root` reaches, the quotient formers excluded.
fn axioms_of(env: &Environment, root: &Name) -> BTreeSet<String> {
    reach(env, root)
        .into_iter()
        .filter(|x| {
            env.get_const(x)
                .is_some_and(|c| c.kind == ConstantKind::Axiom && c.value.is_none())
        })
        .map(|x| x.to_string())
        .filter(|x| !QUOT_FORMERS.contains(&x.as_str()))
        .collect()
}

fn value(env: &Environment, name: &str) -> Expr {
    env.get_const(&n(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("{name} has a value"))
}

fn type_of(env: &Environment, name: &str) -> Expr {
    env.get_const(&n(name))
        .map(|c| c.type_.clone())
        .unwrap_or_else(|| panic!("{name} is declared"))
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_,
        value,
    }
}

fn refused(k: &mut ReferenceKernel, d: Declaration, what: &str) {
    let e = k
        .add_checked(d)
        .expect_err(&format!("{what} must be refused"));
    assert!(
        matches!(e, ReferenceRefusal::Kernel(_)),
        "{what}: got {e:?}"
    );
}

/// `Nat` literal `v` as a kernel term.
fn nat(v: u64) -> Expr {
    Expr::nat_lit(v)
}

#[test]
fn semr_fixture_is_trust_irs_semr_byte_for_byte() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean")
        .join(PINNED)
        .join(FAMILY);
    for (file, pin) in TRUST_IR_COPIES {
        let src = dir.join(file);
        let bytes = std::fs::read(&src).unwrap_or_else(|e| panic!("read {}: {e}", src.display()));
        let digest = Sha256::digest(&bytes);
        let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex, pin,
            "the {file} fixture moved: copy trust-ir's lean/semr/{file} and update its pin \
             here and in trust-ir's lean_exec_differential.rs together"
        );
    }
    for module in MODEL_MODULES {
        let text =
            std::fs::read_to_string(dir.join(format!("{module}.lean"))).expect("UTF-8 source");
        assert_eq!(
            banned_words(&text),
            Vec::<&str>::new(),
            "{module}'s code (comments removed) says a banned word"
        );
    }
}

#[test]
fn semr_fixture_roster_covers_every_source_module() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean")
        .join(PINNED)
        .join(FAMILY);
    let order = std::fs::read_to_string(dir.join("ORDER")).expect("fixture order");
    let ordered: Vec<_> = order
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect();
    assert_eq!(
        ordered, MODEL_MODULES,
        "compile order and complete audit roster"
    );
    let sources: BTreeSet<_> = std::fs::read_dir(&dir)
        .expect("fixture family")
        .map(|entry| {
            let entry = entry.expect("fixture entry");
            assert!(
                entry.file_type().expect("fixture entry type").is_file(),
                "the flat SemR source family must not hide nested or symlinked modules: {}",
                entry.path().display()
            );
            entry.path()
        })
        .filter(|path| path.extension().is_some_and(|ext| ext == "lean"))
        .map(|path| {
            path.file_stem()
                .expect("module stem")
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    assert_eq!(
        sources,
        MODEL_MODULES.into_iter().map(str::to_string).collect()
    );
}

/// Read immutable source objects, including locally imported candidate objects.
/// This does not substitute the declared fixture revision for Cargo's pin:
/// `semr_fixture_is_the_pinned_trust_irs_semr` separately requires that equality.
#[test]
fn semr_fixture_matches_its_declared_source_revision() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean")
        .join(PINNED)
        .join(FAMILY);
    let revision = std::fs::read_to_string(dir.join("SOURCE_REVISION")).expect("source revision");
    assert_eq!(revision.trim(), SEMR_SOURCE_REVISION);
    let repo = std::env::var_os("CLEAN_SEMR_SOURCE_REPO").map(PathBuf::from)
        .or_else(|| trust_ir_checkout(SEMR_SOURCE_REVISION))
        .or_else(|| {
            // A normal fetch creates a checkout for the dependency pin, not
            // for every ancestor. Read the exact source object through that
            // checkout without requiring a separately fetched source revision.
            let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
            let lock = std::fs::read_to_string(root.join("Cargo.lock")).ok()?;
            trust_ir_checkout(&pinned_trust_ir(&lock)?)
        })
        .expect("fetch the pinned trust-ir dependency or set CLEAN_SEMR_SOURCE_REPO to its Git object store");
    for (file, _) in TRUST_IR_COPIES {
        let object = format!("{SEMR_SOURCE_REVISION}:lean/semr/{file}");
        let output = std::process::Command::new("git")
            .arg("-C")
            .arg(&repo)
            .args(["cat-file", "blob", &object])
            .output()
            .expect("read source Git object");
        assert!(
            output.status.success(),
            "{object}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            std::fs::read(dir.join(file)).expect("fixture bytes"),
            output.stdout,
            "{file}: fixture differs from its actual source object"
        );
    }
}

/// `MiniRust.lean` is the `trust_sem` family's `SpecrPrelude.lean` followed by
/// its `MiniRustSlice.lean`, in a `noncomputable section`, byte for byte: the
/// same two files RM1 checks (Trust's `regen.py check` compares those copies
/// with Trust's `scripts/trust_core/specr/`), so SemR's MiniRust operators are
/// the translator's, not a hand copy.
#[test]
fn semr_minirust_copy_is_the_trust_sem_slice() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean")
        .join(PINNED);
    let read = |family: &str, file: &str| {
        let p = fixtures.join(family).join(file);
        std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
    };
    let want = format!(
        "noncomputable section\n{}{}\nend\n",
        read("trust_sem", "SpecrPrelude.lean"),
        read("trust_sem", "MiniRustSlice.lean")
    );
    assert!(
        read(FAMILY, "MiniRust.lean") == want,
        "semr/MiniRust.lean is not the trust_sem prelude and slice in a noncomputable section"
    );
}

/// Historical pre-SemR revision, retained only as a negative control. The
/// current witness must compare real sources even when offered this revision.
const TRUST_IR_BEFORE_SEMR: &str = "64a2a8397ffe1e7dfe737b8fe92392ef00741b32";

/// The actual SemR witness consumed by clean-olean, independently of the older
/// production compiler cohort. Every Cargo dependency-ID form must identify
/// exactly one immutable package row; lockfile ordering grants no authority.
fn pinned_trust_ir(lock: &str) -> Option<String> {
    let parsed = lock.parse::<toml::Table>().ok()?;
    let packages = parsed.get("package")?.as_array()?;
    let consumers: Vec<_> = packages
        .iter()
        .filter(|p| p.get("name").and_then(toml::Value::as_str) == Some("clean-olean"))
        .collect();
    let [consumer] = consumers.as_slice() else {
        return None;
    };
    let dependencies: Vec<_> = consumer
        .get("dependencies")?
        .as_array()?
        .iter()
        .filter_map(toml::Value::as_str)
        .filter(|id| *id == "trust-ir" || id.starts_with("trust-ir "))
        .collect();
    let [dependency] = dependencies.as_slice() else {
        return None;
    };
    let matches: Vec<_> = packages
        .iter()
        .filter(|p| p.get("name").and_then(toml::Value::as_str) == Some("trust-ir"))
        // Resolve over ALL matching rows before authenticating the source.
        // Discarding a registry/path/foreign row first could hide ambiguity.
        .filter(|p| {
            if *dependency == "trust-ir" {
                return true;
            }
            let Some(version) = p.get("version").and_then(toml::Value::as_str) else {
                return false;
            };
            if *dependency == format!("trust-ir {version}") {
                return true;
            }
            let Some(source) = p.get("source").and_then(toml::Value::as_str) else {
                return false;
            };
            let selector = source.rsplit_once('#').map_or(source, |(id, _)| id);
            *dependency == format!("trust-ir {version} ({selector})")
        })
        .collect();
    let [resolved] = matches.as_slice() else {
        return None;
    };
    let (selector, revision) = resolved.get("source")?.as_str()?.rsplit_once('#')?;
    if revision.len() != 40
        || !revision
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
        || selector != format!("git+https://github.com/alabsystems/trust-ir.git?rev={revision}")
    {
        return None;
    }
    Some(revision.to_string())
}

/// Cargo's checkout of trust-ir at `rev` (`$CARGO_HOME/git/checkouts/
/// trust-ir-*/<rev[..7]>`), when one is on this host.
fn trust_ir_checkout(rev: &str) -> Option<PathBuf> {
    let home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")))?;
    let checkouts = home.join("git/checkouts");
    let mut found: Vec<PathBuf> = std::fs::read_dir(&checkouts)
        .ok()?
        .filter_map(Result::ok)
        .filter(|e| e.file_name().to_string_lossy().starts_with("trust-ir-"))
        .map(|e| e.path().join(&rev[..7]))
        .filter(|p| p.join("crates/trust-ir/Cargo.toml").is_file())
        .collect();
    found.sort();
    found.into_iter().next()
}

/// SemR has one source: trust-ir's `lean/semr/SemR.lean` at the trust-ir
/// revision Clean pins, which this fixture copies. Each repository pins only
/// its own copy's digest (`SEMR_SHA256` here, `SEMR_SOURCE_SHA256` there), so
/// a coordinated change of a copy and its constant in one repository passes
/// that repository's digest test; this judge compares the copies themselves.
/// It is one-directional (trust-ir owns the format, Clean follows), so the
/// two repositories never wait on each other: trust-ir lands a SemR change,
/// and the Clean commit that moves its trust-ir pin past it carries the new
/// copy. A historical production-pin transition grants no witness exemption.
fn judge_semr_copy(
    rev: &str,
    checkout: Option<&Path>,
    file: &str,
    fixture: &[u8],
) -> Result<(), String> {
    let root = checkout.ok_or_else(|| {
        format!("no checkout of trust-ir {rev} on this host (`targo fetch` makes one)")
    })?;
    let source = root.join("lean/semr").join(file);
    let bytes = std::fs::read(&source).map_err(|e| {
        format!(
            "trust-ir {rev} carries no {} ({e}), but Clean pins it past the last revision \
             without SemR",
            source.display()
        )
    })?;
    if bytes == fixture {
        Ok(())
    } else {
        let hex = |b: &[u8]| -> String {
            Sha256::digest(b)
                .iter()
                .map(|x| format!("{x:02x}"))
                .collect()
        };
        Err(format!(
            "the fixture copy (sha256 {}) differs from trust-ir {rev}'s lean/semr/{file} \
             (sha256 {}): copy it over and set its pin in the commit that moves the pin",
            hex(fixture),
            hex(&bytes)
        ))
    }
}

/// The copies here are the sources at the trust-ir revision Clean pins.
#[test]
fn semr_fixture_is_the_pinned_trust_irs_semr() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let lock = std::fs::read_to_string(root.join("Cargo.lock")).expect("Clean's Cargo.lock");
    let rev = pinned_trust_ir(&lock).expect("Cargo.lock resolves clean-olean's exact SemR witness");
    let checkout = trust_ir_checkout(&rev);
    for (file, _) in TRUST_IR_COPIES {
        let fixture = std::fs::read(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/lean")
                .join(PINNED)
                .join(FAMILY)
                .join(file),
        )
        .expect("the SemR fixture");
        judge_semr_copy(&rev, checkout.as_deref(), file, &fixture)
            .unwrap_or_else(|e| panic!("{e}"));
    }
}

/// The judge's controls, over checkouts this test writes: the same bytes
/// pass; one changed byte, a checkout without SemR and no checkout at all
/// each fail. The historical pre-SemR revision grants no exemption.
#[test]
fn semr_copy_judge_controls() {
    let scratch = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("semr-copy-judge-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&scratch);
    let with = scratch.join("with/lean/semr");
    std::fs::create_dir_all(&with).expect("scratch");
    std::fs::create_dir_all(scratch.join("without/lean")).expect("scratch");
    let fixture = b"namespace SemR\nend SemR\n".to_vec();
    std::fs::write(with.join("SemR.lean"), &fixture).expect("write");
    let later = "1111111111111111111111111111111111111111";
    let with_root = scratch.join("with");
    let without_root = scratch.join("without");
    assert_eq!(
        judge_semr_copy(later, Some(&with_root), "SemR.lean", &fixture),
        Ok(())
    );
    let mut changed = fixture.clone();
    changed[0] ^= 1;
    assert!(
        judge_semr_copy(later, Some(&with_root), "SemR.lean", &changed)
            .unwrap_err()
            .contains("differs")
    );
    assert!(
        judge_semr_copy(later, Some(&without_root), "SemR.lean", &fixture)
            .unwrap_err()
            .contains("carries no")
    );
    assert!(judge_semr_copy(later, None, "SemR.lean", &fixture)
        .unwrap_err()
        .contains("no checkout"));
    assert!(
        judge_semr_copy(TRUST_IR_BEFORE_SEMR, None, "SemR.lean", &changed)
            .unwrap_err()
            .contains("no checkout")
    );
    assert!(judge_semr_copy(
        TRUST_IR_BEFORE_SEMR,
        Some(&with_root),
        "ClosureConstruction.lean",
        &changed,
    )
    .unwrap_err()
    .contains("carries no"));
    let _ = std::fs::remove_dir_all(&scratch);
}

#[test]
fn semr_source_pin_follows_its_actual_consumer_edge() {
    let before = TRUST_IR_BEFORE_SEMR;
    let current = SEMR_SOURCE_REVISION;
    let package = |rev: &str| {
        format!(
            "[[package]]\nname = \"trust-ir\"\nversion = \"0.14.0\"\nsource = \
         \"git+https://github.com/alabsystems/trust-ir.git?rev={rev}#{rev}\"\n\n"
        )
    };
    let consumer = |revs: &[&str]| {
        let ids = revs
            .iter()
            .map(|rev| {
                format!(
            "\"trust-ir 0.14.0 (git+https://github.com/alabsystems/trust-ir.git?rev={rev})\""
        )
            })
            .collect::<Vec<_>>()
            .join(",\n");
        format!(
            "[[package]]\nname = \"clean-olean\"\nversion = \"0.9.0\"\ndependencies = [{ids}]\n\n"
        )
    };
    let edge = consumer(&[current]);
    for lock in [
        format!("{}{}{}", package(before), package(current), edge),
        format!("{}{}{}", package(current), edge, package(before)),
    ] {
        assert_eq!(pinned_trust_ir(&lock).as_deref(), Some(current));
    }
    let qualified = format!(
        "trust-ir 0.14.0 (git+https://github.com/alabsystems/trust-ir.git?rev={current})"
    );
    let foreign = package(before).replace("alabsystems/trust-ir", "somebody-else/trust-ir");
    let registry = "[[package]]\nname = \"trust-ir\"\nversion = \"0.14.0\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n\n";
    let path = "[[package]]\nname = \"trust-ir\"\nversion = \"0.14.0\"\n\n";
    for id in ["trust-ir", "trust-ir 0.14.0"] {
        let compact = edge.replace(&qualified, id);
        assert_eq!(
            pinned_trust_ir(&format!("{compact}{}", package(current))).as_deref(),
            Some(current)
        );
        for competing in [
            package(before),
            foreign.clone(),
            registry.to_string(),
            path.to_string(),
        ] {
            assert_eq!(
                pinned_trust_ir(&format!("{compact}{}{competing}", package(current))),
                None,
                "{id}: every matching package counts before source validation"
            );
        }
        assert_eq!(
            pinned_trust_ir(&format!("{compact}{foreign}")),
            None,
            "unique foreign source"
        );
    }
    assert_eq!(pinned_trust_ir(&package(current)), None, "no consumer");
    assert_eq!(
        pinned_trust_ir(&format!("{edge}{}", package(before))),
        None,
        "unresolved edge"
    );
    assert_eq!(
        pinned_trust_ir(&format!("{edge}{edge}{}", package(current))),
        None,
        "ambiguous consumer"
    );
    assert_eq!(
        pinned_trust_ir(&format!(
            "{}{}{}",
            consumer(&[before, current]),
            package(before),
            package(current)
        )),
        None,
        "ambiguous edge"
    );
    assert_eq!(
        pinned_trust_ir(&format!("{edge}{}{}", package(current), package(current))),
        None,
        "duplicate package"
    );
    let coherent = format!("{edge}{}", package(current));
    assert_eq!(
        pinned_trust_ir(&coherent.replace(&format!("#{current}"), &format!("#{before}"))),
        None,
        "selector/hash mismatch"
    );
    assert_eq!(
        pinned_trust_ir(&coherent.replace("alabsystems/trust-ir", "someone-else/trust-ir")),
        None,
        "foreign repository"
    );
}

/// The tripwire's lexer, by case: what a comment hides is not code; what a
/// string or character literal holds is (fail closed); a literal cannot open
/// a comment or a string. The negative controls are the review's bypass
/// (`'"'` opening a fake string) and its relatives.
#[test]
fn semr_tripwire_lexes_strings_characters_and_comments() {
    // Comments are removed (positive control: SemR's own prose names every
    // banned word in comments).
    assert_eq!(
        banned_words("-- native_decide\ndef x := 1"),
        Vec::<&str>::new()
    );
    assert_eq!(
        banned_words("/- partial /- nested -/ sorry -/ def x := 1"),
        Vec::<&str>::new()
    );
    assert_eq!(
        banned_words("/-- doc: axiom -/ def x := 1"),
        Vec::<&str>::new()
    );
    // A prime is not a character literal.
    assert_eq!(banned_words("def k' := k'' -- sorry"), Vec::<&str>::new());
    // The review's bypass: `'"'` must not open a string.
    assert_eq!(
        banned_words("def dq : Char := '\"'\ntheorem smuggled : 10 < 11 := by native_decide"),
        vec!["native_decide"]
    );
    assert_eq!(
        banned_words("def dq : Char := '\"'\npartial def spin (n : Nat) : Nat := spin n"),
        vec!["partial"]
    );
    // An escaped quote character, and an escaped quote in a string.
    assert_eq!(
        banned_words(
            "def q : Char := '\\''\ndef s := \"a\\\"b\" -- x\ntheorem t : True := by sorry"
        ),
        vec!["sorry"]
    );
    // A comment opener inside a string or a character opens nothing.
    assert_eq!(
        banned_words("def s := \"a -- b\" ++ (by native_decide)"),
        vec!["native_decide"]
    );
    assert_eq!(
        banned_words("def s := \"/-\"\ndef t := 1\naxiom a : False\n-/"),
        vec!["axiom"]
    );
    assert_eq!(
        banned_words("def c : Char := '-'\n-- x\nopaque o : Nat"),
        vec!["opaque"]
    );
    // A string's own text is kept (fail closed).
    assert_eq!(banned_words("def s := \"unsafe\""), vec!["unsafe"]);
    // An interpolation's code may hold strings of its own.
    assert_eq!(
        banned_words("def s := s!\"{f \"}\"} x\" ++ \"-- y\"\n@[extern \"c\"] def e := 1"),
        vec!["extern"]
    );
    // What the lexer does not model, or a text that ends mid-literal, panics.
    for bad in [
        "def s := r\"raw\"",
        "def s := \"open",
        "/- open",
        "def s := s!\"{x\"",
    ] {
        assert!(
            std::panic::catch_unwind(|| lean_code_only(bad)).is_err(),
            "`{bad}` must not pass the lexer"
        );
    }
}

/// The forged family's source trips the tripwire (its `'"'` included).
#[test]
fn semr_tripwire_catches_the_forged_fixture() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean")
        .join(PINNED)
        .join(FORGED_FAMILY)
        .join("SemRForged.lean");
    let text = std::fs::read_to_string(&src).unwrap_or_else(|e| panic!("{}: {e}", src.display()));
    assert_eq!(banned_words(&text), vec!["native_decide", "partial"]);
}

/// The negative-control family: SemR-named constants smuggled behind a
/// character literal (`semr_forged/SemRForged.lean`).
const FORGED_FAMILY: &str = "semr_forged";

/// The kernel declarations a compiled module of `family` makes, read off its
/// own `.olean` (`constNames`/`constants`: `_root_` declarations are in it),
/// each with its declared safety, and the number of the compiler's names
/// beside them (`extraConstNames`: `_boxed`, `_closed_N`, `_lam_N`,
/// `_redArg`, `spec_N`, which are not kernel declarations and are not in the
/// loaded environment). A module split into parts (`.olean.private`, …) is
/// refused: its private part would go unread.
fn module_constants(
    family_dir: &Path,
    module: &str,
) -> (Vec<(Name, Option<DefinitionSafety>)>, usize) {
    let path = family_dir.join(format!("{module}.olean"));
    for part in ["olean.private", "olean.server"] {
        let sibling = family_dir.join(format!("{module}.{part}"));
        assert!(
            !sibling.exists(),
            "{} exists: a split module",
            sibling.display()
        );
    }
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed = parse_module(&bytes).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
    let listed: BTreeSet<&str> = parsed.const_names.iter().map(String::as_str).collect();
    let carried: BTreeSet<&str> = parsed.constants.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(listed, carried, "{module}: constNames and constants agree");
    let decls = parsed
        .constants
        .iter()
        .map(|c| (n(&c.name), c.definition_safety))
        .collect();
    (decls, parsed.extra_const_names.len())
}

/// Admit every kernel declaration `modules` of `family` make through the
/// entry, and audit each: admitted, neither an axiom nor opaque, closure ⊆
/// Ax0 and no native-evaluation or sorry constant in its cone. The
/// declarations whose safety is `unsafe` or `partial` must be the compiler's
/// twins (`<definition>._unsafe_rec`, beside each recursive definition and
/// each `partial def`, whose own constant is opaque and so reported): they
/// are not in the loaded environment, so a cone that reached one would fail
/// the replay, and the source tripwire refuses the words `unsafe` and
/// `partial` in SemR's code; they, and the compiler's non-kernel names, are
/// counted and set aside. Any other unsafe or partial declaration is a
/// violation. Returns the entry built, every violation by constant, and the
/// numbers set aside (compiler twins, compiler names).
fn audit_modules(
    env: &Environment,
    family_dir: &Path,
    modules: &[&str],
) -> (clean_olean::ReferenceBase, Vec<String>, (usize, usize)) {
    let mut declared: BTreeSet<Name> = BTreeSet::new();
    let mut violations: Vec<String> = Vec::new();
    let (mut unsafe_aux, mut compiler_names) = (0usize, 0usize);
    for module in modules {
        let (decls, extra) = module_constants(family_dir, module);
        compiler_names += extra;
        for (name, safety) in decls {
            match safety {
                Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial) => {
                    if name.to_string().ends_with("._unsafe_rec") {
                        unsafe_aux += 1;
                    } else {
                        violations.push(format!(
                            "{name}: is a {safety:?} declaration that is not a compiler twin"
                        ));
                    }
                }
                _ => {
                    declared.insert(name);
                }
            }
        }
    }
    assert!(!declared.is_empty(), "the modules declare constants");
    let built =
        reference_base_closed(env, &declared, &ClosedRecheckOptions::default()).expect("start");
    if !built.report.passed() {
        violations.push(format!("replay: {}", built.report.verdict_sentence()));
        for refusal in &built.report.refusals {
            violations.push(format!("replay refusal: {refusal:?}"));
        }
    }
    for (unit, refusal) in &built.entry_refusals {
        violations.push(format!("{unit}: refused by the entry: {refusal:?}"));
    }
    let ax0: BTreeSet<String> = AX0.iter().map(|s| (*s).to_string()).collect();
    let k = built.kernel().environment();
    for name in &declared {
        let present = k.get_const(name).is_some()
            || k.get_inductive(name).is_some()
            || k.get_constructor(name).is_some()
            || k.get_recursor(name).is_some();
        if !present {
            violations.push(format!("{name}: not admitted through the entry"));
            continue;
        }
        if let Some(c) = k.get_const(name) {
            if matches!(c.kind, ConstantKind::Axiom | ConstantKind::Opaque) {
                violations.push(format!("{name}: is an {:?} constant", c.kind));
            }
        }
        let closure = axioms_of(k, name);
        if !closure.is_subset(&ax0) {
            violations.push(format!("{name}: closure {closure:?} is not ⊆ Ax0"));
        }
        let cone = reach(k, name);
        for bad in [
            "sorryAx",
            "Lean.ofReduceBool",
            "Lean.ofReduceNat",
            "Lean.trustCompiler",
        ] {
            if cone.contains(&n(bad)) {
                violations.push(format!("{name}: reaches {bad}"));
            }
        }
    }
    (built, violations, (unsafe_aux, compiler_names))
}

/// NEGATIVE CONTROL of the audit: over the forged family, the smuggled
/// `native_decide` theorem and the `partial def` are each reported by name,
/// and the honest declarations beside them are not. Release-only, as the
/// audit it controls is: the unoptimized replay of even this small cone
/// (`Char`'s, `Nat.decLt`'s) runs past twenty minutes.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "unoptimized replay of the cone takes many minutes; run with --release or --ignored"
)]
fn semr_audit_reports_smuggled_constants() {
    let lib = pinned_lib();
    let dir = compiled_fixture_dir(FORGED_FAMILY);
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(&mut env, "SemRForged", &[dir.clone(), lib])
        .unwrap_or_else(|e| panic!("load SemRForged: {e}"));
    let (_, violations, (unsafe_aux, _)) = audit_modules(&env, &dir, &["SemRForged"]);
    assert!(
        unsafe_aux >= 1,
        "`partial def spin` has an unsafe implementation"
    );
    let about = |name: &str| {
        violations
            .iter()
            .any(|v| v.starts_with(&format!("{name}:")))
    };
    assert!(
        about("SemR.smuggled"),
        "the native_decide theorem: {violations:#?}"
    );
    assert!(about("SemR.spin"), "the partial def: {violations:#?}");
    for honest in ["SemR.dq", "SemR.honest", "SemR.honest_eq"] {
        assert!(!about(honest), "{honest} is honest: {violations:#?}");
    }
}

/// Measured 2026-10-26 in `--release`; the unoptimized replay of `Init`'s cone is
/// far slower, so a debug run skips it unless `--ignored` asks.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "unoptimized replay of the cone takes many minutes; run with --release or --ignored"
)]
fn semr_theorems_are_admitted_through_the_entry_with_closure_in_ax0() {
    let lib = pinned_lib();
    let mut env = Environment::for_lean_replay();
    let dir = compiled_fixture_dir(FAMILY);
    lean_axiom_census::check(
        &clean_olean::pinned_lean_binary().expect("the pinned Lean toolchain"),
        &dir,
        MODULE,
        EXPECTED,
    );
    // The audit covers the entire roster, including independent modules that
    // SemRCheck does not import. Load that same union before selecting roots.
    let modules: Vec<String> = MODEL_MODULES
        .iter()
        .map(|module| (*module).to_owned())
        .collect();
    let summaries = load_modules_with_deps(&mut env, &modules, &[dir, lib])
        .unwrap_or_else(|e| panic!("load full SemR roster: {e}"));
    let loaded_modules: BTreeSet<_> = summaries
        .iter()
        .filter_map(|summary| summary.module_name.as_deref())
        .collect();
    for module in MODEL_MODULES {
        assert!(
            loaded_modules.contains(module),
            "audit module was not loaded: {module}"
        );
    }

    // Every constant SemR and SemRCheck declare, not only the theorems' cones.
    let (built, violations, (unsafe_aux, compiler_names)) =
        audit_modules(&env, &compiled_fixture_dir(FAMILY), &MODEL_MODULES);
    assert!(
        violations.is_empty(),
        "{} audit violation(s):\n  {}",
        violations.len(),
        violations.join("\n  ")
    );
    for (t, _) in EXPECTED {
        assert!(
            built.admitted.contains(&n(t)),
            "{t} was not admitted through the entry"
        );
    }
    // SemR itself went through the entry, not only the theorems about it.
    for generated in [
        "SemR.decode",
        "SemR.run",
        "SemR.stepCore",
        "SemR.intBin",
        "SemR.moduleBody",
        "SemR.Step",
        "SemR.binopStep",
        "SemR.allocAt",
        "SemR.gepAt",
        "SemR.Allocates",
        "SemR.Offsets",
        "SemR.pow_bytes_target",
        "SemR.readOut_after_store_target",
        "MRf.Machine.eval_bin_op",
        "MRf.Machine.eval_un_op",
    ] {
        assert!(
            built.admitted.contains(&n(generated)),
            "{generated} was not admitted through the entry"
        );
    }
    eprintln!(
        "semr_reference: {} constants admitted through the entry; every declared constant \
         audited; set aside: {unsafe_aux} unsafe compiler twins, {compiler_names} compiler names",
        built.admitted.len()
    );
    let mut k = built.into_kernel().expect("a passing, pinned replay");
    assert_eq!(k.theory_id(), TheoryId::LeanReferenceV1);

    // ── Closures, read from the entry's own environment. ──
    let ax0: BTreeSet<String> = AX0.iter().map(|s| (*s).to_string()).collect();
    for (t, want) in EXPECTED {
        let got = axioms_of(k.environment(), &n(t));
        let want: BTreeSet<String> = want.iter().map(|s| (*s).to_string()).collect();
        assert_eq!(got, want, "{t}: closure differs from Lean's #print axioms");
        assert!(got.is_subset(&ax0), "{t}: closure {got:?} is not ⊆ Ax0");
        let r = reach(k.environment(), &n(t));
        for bad in [
            "sorryAx",
            "Lean.ofReduceBool",
            "Lean.ofReduceNat",
            "Lean.trustCompiler",
        ] {
            assert!(!r.contains(&n(bad)), "{t} reaches {bad}");
        }
    }

    // The real pointer-return proof preserves the captured offset; reusing it
    // for offset 12 after capture of offset 11 must fail through the same entry.
    let specialise_pointer = |offset| {
        let mut statement = type_of(&env, "SemR.closure_direct_pointer_return");
        for argument in [7, offset] {
            let ExprKind::Pi(_, _, body) = statement.kind() else {
                panic!("pointer-return theorem lost its two Nat binders");
            };
            statement = body.instantiate(&nat(argument));
        }
        statement
    };
    let genuine_pointer = specialise_pointer(11);
    let changed_pointer = specialise_pointer(12);
    let genuine_args = genuine_pointer.get_app_args();
    let changed_args = changed_pointer.get_app_args();
    let ([ty, lhs, _], [_, _, wrong_rhs]) = (genuine_args.as_slice(), changed_args.as_slice())
    else {
        panic!("pointer-return theorem is no longer an equality");
    };
    let forged_pointer = Expr::apps(
        genuine_pointer.get_app_fn().clone(),
        [(*ty).clone(), (*lhs).clone(), (*wrong_rhs).clone()],
    );
    let pointer_proof = Expr::apps(
        value(&env, "SemR.closure_direct_pointer_return"),
        [nat(7), nat(11)],
    );
    k.add_checked(theorem(
        "SemRCheck.closure_projection_pointer_control",
        genuine_pointer.clone(),
        pointer_proof.clone(),
    ))
    .expect("control: the real capture projection preserves pointer offset 11");
    refused(
        &mut k,
        theorem(
            "SemRCheck.forged_closure_projection_offset",
            forged_pointer,
            pointer_proof,
        ),
        "capture projection changes pointer offset 11 to 12",
    );

    // ── Negative control 1: a kernel-evaluated run claimed with the wrong result. ──
    let run_is =
        |a: u64, b: u64, r: u64| Expr::apps(c("SemRCheck.RunIs"), [nat(a), nat(b), nat(r)]);
    let proof = value(&env, "SemRCheck.sub_5_3");
    k.add_checked(theorem(
        "SemRCheck.semr_control_sub",
        run_is(5, 3, 2),
        proof.clone(),
    ))
    .expect("control: the genuine computed run is accepted");
    refused(
        &mut k,
        theorem("SemRCheck.semr_forged_sub", run_is(5, 3, 3), proof),
        "sub(5, 3) = 3",
    );

    // ── Negative control 2: the decode verdict of a corrupted blob, flipped. ──
    let decodes_true = type_of(&env, "SemRCheck.blob_decodes");
    k.add_checked(theorem(
        "SemRCheck.semr_control_decodes",
        decodes_true,
        value(&env, "SemRCheck.blob_decodes"),
    ))
    .expect("control: the genuine decode verdict is accepted");
    let trailing = type_of(&env, "SemRCheck.trailing_byte_refused");
    let flipped = match trailing.get_app_args().as_slice() {
        [ty, lhs, _] => Expr::apps(
            trailing.get_app_fn().clone(),
            [(*ty).clone(), (*lhs).clone(), c("Bool.true")],
        ),
        other => panic!("trailing_byte_refused is `@Eq Bool (decodes …) false`, got {other:?}"),
    };
    refused(
        &mut k,
        theorem(
            "SemRCheck.semr_forged_trailing",
            flipped,
            value(&env, "SemRCheck.blob_decodes"),
        ),
        "a blob with a trailing byte decodes",
    );

    // ── Negative control 3: run_sound's proof offered for ForgedRunSound. ──
    refused(
        &mut k,
        theorem(
            "SemRCheck.semr_forged_run_sound",
            c("SemRCheck.ForgedRunSound"),
            value(&env, "SemR.run_sound"),
        ),
        "run_sound proves that every run is out of fuel",
    );
    k.add_checked(theorem(
        "SemRCheck.semr_control_forged_fails",
        type_of(&env, "SemRCheck.forged_run_sound_fails"),
        value(&env, "SemRCheck.forged_run_sound_fails"),
    ))
    .expect("control: the refutation of ForgedRunSound is accepted");

    // ── Negative control 4: step_complete's proof offered for ForgedStep. ──
    refused(
        &mut k,
        theorem(
            "SemRCheck.semr_forged_step",
            c("SemRCheck.ForgedStep"),
            value(&env, "SemR.step_complete"),
        ),
        "step_complete proves that every state steps out of fuel",
    );
    k.add_checked(theorem(
        "SemRCheck.semr_control_forged_step_fails",
        type_of(&env, "SemRCheck.forged_step_fails"),
        value(&env, "SemRCheck.forged_step_fails"),
    ))
    .expect("control: the refutation of ForgedStep is accepted");

    // ── Negative control 5: MiniRust's i8 MIN / -1 claimed to be a value. ──
    k.add_checked(theorem(
        "SemRCheck.semr_control_i8_min_div",
        type_of(&env, "SemRCheck.i8_min_div_neg_one"),
        value(&env, "SemRCheck.i8_min_div_neg_one"),
    ))
    .expect("control: the genuine operator instance is accepted");
    refused(
        &mut k,
        theorem(
            "SemRCheck.semr_forged_sdiv",
            c("SemRCheck.ForgedSdiv"),
            value(&env, "SemRCheck.i8_min_div_neg_one"),
        ),
        "MiniRust's i8 MIN / -1 is a value",
    );
    k.add_checked(theorem(
        "SemRCheck.semr_control_forged_sdiv_fails",
        type_of(&env, "SemRCheck.forged_sdiv_fails"),
        value(&env, "SemRCheck.forged_sdiv_fails"),
    ))
    .expect("control: the refutation of ForgedSdiv is accepted");

    // ── Negative controls 6 and 7: the signed `and` and `ctpop` instances,
    //    their proofs offered for a forged result (`-1 & -128 = 0`, seven
    //    ones in `-1`), refused beside the accepted genuine instances and
    //    refutations. ──
    for (instance, forged, refutation, what) in [
        (
            "SemR.construction_instruction_v63_refused",
            "SemRCheck.ForgedClosureWire",
            "SemRCheck.forged_closure_wire_fails",
            "quoted closure construction opens the v63 wire decoder",
        ),
        (
            "SemRCheck.i8_and_signed",
            "SemRCheck.ForgedAndSigned",
            "SemRCheck.forged_and_signed_fails",
            "MiniRust's i8 -1 & -128 is 0",
        ),
        (
            "SemRCheck.i8_ctpop_neg_one",
            "SemRCheck.ForgedCtpop",
            "SemRCheck.forged_ctpop_fails",
            "MiniRust counts seven ones in the i8 -1",
        ),
        (
            "SemRCheck.mem_load_after_dealloc",
            "SemRCheck.ForgedUseAfterFree",
            "SemRCheck.forged_use_after_free_fails",
            "a load after StorageDead reads the slot's old value",
        ),
        (
            "SemRCheck.mem_byte_one",
            "SemRCheck.ForgedBigEndian",
            "SemRCheck.forged_big_endian_fails",
            "byte 1 of a stored u32 is its big-endian byte",
        ),
        (
            "SemRCheck.u32_encode",
            "SemRCheck.ForgedEncode",
            "SemRCheck.forged_encode_fails",
            "MiniRust encodes a u32 big-endian",
        ),
        (
            "SemRCheck.i32_decode",
            "SemRCheck.ForgedDecode",
            "SemRCheck.forged_decode_fails",
            "MiniRust decodes an i32's bytes unsigned",
        ),
        (
            "SemRCheck.misaligned_1025",
            "SemRCheck.ForgedAligned",
            "SemRCheck.forged_aligned_fails",
            "MiniRust calls address 1025 aligned to 4",
        ),
        (
            "SemRCheck.dead_slot_check_ptr",
            "SemRCheck.ForgedDeadAccess",
            "SemRCheck.forged_dead_access_fails",
            "MiniRust's check_ptr lets a load through a dead slot",
        ),
    ] {
        k.add_checked(theorem(
            &format!("{instance}_control"),
            type_of(&env, instance),
            value(&env, instance),
        ))
        .unwrap_or_else(|e| panic!("control: the genuine {instance} is accepted: {e:?}"));
        refused(
            &mut k,
            theorem(
                &format!("{forged}_by_instance"),
                c(forged),
                value(&env, instance),
            ),
            what,
        );
        k.add_checked(theorem(
            &format!("{refutation}_control"),
            type_of(&env, refutation),
            value(&env, refutation),
        ))
        .unwrap_or_else(|e| panic!("control: {refutation} is accepted: {e:?}"));
    }

    // Target-width forgeries are checked beside their genuine 32/64 controls.
    for (instance, forged, refutation, what) in [
        (
            "SemRCheck.usize64_footprint",
            "SemRCheck.WrongUsize32Footprint",
            "SemRCheck.wrong_usize32_footprint_refused",
            "a 64-bit usize footprint proves eight bytes on wasm32",
        ),
        (
            "SemRCheck.same_allocation64_fits",
            "SemRCheck.WrongAllocation32",
            "SemRCheck.wrong_allocation32_refused",
            "a 64-bit allocation result proves an overflowing wasm32 allocation",
        ),
        (
            "SemRCheck.usize32_image",
            "SemRCheck.WrongUsize32Image",
            "SemRCheck.wrong_usize32_image_refused",
            "a four-byte usize image proves an eight-byte image on wasm32",
        ),
    ] {
        k.add_checked(theorem(
            &format!("{instance}_control"),
            type_of(&env, instance),
            value(&env, instance),
        ))
        .unwrap_or_else(|e| panic!("genuine target control {instance}: {e:?}"));
        refused(
            &mut k,
            theorem(
                &format!("{forged}_by_wrong_target"),
                c(forged),
                value(&env, instance),
            ),
            what,
        );
        k.add_checked(theorem(
            &format!("{refutation}_control"),
            type_of(&env, refutation),
            value(&env, refutation),
        ))
        .unwrap_or_else(|e| panic!("target refutation {refutation}: {e:?}"));
    }
}
