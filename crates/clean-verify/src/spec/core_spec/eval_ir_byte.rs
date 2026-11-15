// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Versioned byte/world EvalIR construction and final-state-preserving driver.
//! These are operational definitions, not a native-code admission certificate.

use crate::spec::{SpecError, Specification};
use clean_kernel::Name;

impl Specification {
    /// Build the byte/world profile in the ordinary Clean prelude.
    ///
    /// The actual module and its exact reflected context are explicit semantic
    /// inputs. External providers and the initial byte/host world are also
    /// inputs, not assumptions that a particular runtime or installed image
    /// implements them. This preserves the legacy EvalIR declarations.
    ///
    /// The v1 execution domain is canonical 64-bit little-endian, with C/Fast
    /// calls, scalar byte accesses, array allocation and SSA struct values.
    /// Opt-in enum schemas additionally admit tagged SSA values with complete
    /// payload typing; old contexts still refuse enums. This adds neither enum
    /// memory decoding nor an authenticated Rust-to-schema producer binding.
    /// Relaxed U64 and distinct target-indexed Usize64 fetch-add instructions
    /// have sequential byte semantics; concurrent interference and source
    /// atomicity are not modeled here. Other Usize widths remain refused.
    /// Five distinct fat-pointer kinds support typed SSA data/metadata/parts
    /// transport with bounded LE64 words. This does not admit fat-pointer
    /// memory, casts, dereference, general string validity or vtable dispatch.
    /// An exact builtin-name observer checks initialized ASCII Nat/String
    /// bytes behind an already projected FatStr view and live allocation.
    /// It does not establish that view from a Rust Arc/Name/Expr layout.
    /// It is not a second module validator: valid reachable SSA/branch typing
    /// is a premise of a relation using this evaluator. Address-only inbounds
    /// GEP also requires unambiguous allocation boundaries; arbitrary adjacent
    /// external regions need a separate representation/provenance rule. The
    /// allocator's own live regions have guard gaps. Provider behavior and
    /// code/data image separation remain explicit representation obligations.
    ///
    /// Every newly installed value-bearing root is independently type-checked
    /// and audited for domain-specific axioms and trust markers. Definition bookkeeping is not
    /// promoted into source-translation or native-execution proof authority.
    ///
    /// # Errors
    /// Fails on elaboration, kernel checking, missing terms, or any new root
    /// depending on a domain-specific axiom or trust marker.
    pub fn new_eval_ir_byte_prelude_spec_v1() -> Result<Self, SpecError> {
        let mut spec = Self::new_eval_ir_prelude_spec()?;
        let previous: std::collections::HashSet<String> =
            spec.definitions().keys().cloned().collect();
        spec.add_eval_ir_driver()?;
        spec.add_eval_ir_byte_stages_v1()?;
        spec.verify_eval_ir_byte_additions_v1(&previous)?;
        Ok(spec)
    }

    // The completed Full model already owns the five checked driver roots.
    // Keep driver installation at the caller; do not silently skip duplicate
    // declarations or narrow the prelude constructor's audited delta.
    pub(super) fn add_eval_ir_byte_stages_v1(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_byte_types()?;
        self.add_eval_ir_byte_memory()?;
        self.add_eval_ir_byte_fat_v1()?;
        self.add_eval_ir_byte_cast_v1()?;
        self.add_eval_ir_byte_radix_laws_v1()?;
        self.add_eval_ir_byte_alignment_laws_v1()?;
        self.add_eval_ir_byte_codec_laws()?;
        self.add_eval_ir_byte_memory_laws()?;
        self.add_eval_ir_byte_scalar_laws_v1()?;
        self.add_eval_ir_integer_multiplication_law_v1()?;
        self.add_eval_ir_byte_function_laws_v1()?;
        self.add_eval_ir_byte_access_laws_v1()?;
        self.add_eval_ir_byte_lifetime_laws_v1()?;
        self.add_eval_ir_byte_atomic_v1()?;
        self.add_eval_ir_byte_usize_v1()?;
        self.add_eval_ir_byte_usize_cmp_v1()?;
        self.add_eval_ir_byte_const_v1()?;
        self.add_eval_ir_byte_field_v1()?;
        self.add_eval_ir_byte_gep_typed_v1()?;
        self.add_eval_ir_byte_machine()?;
        self.add_eval_ir_byte_world_laws_v1()?;
        self.add_eval_ir_byte_allocation_laws_v1()?;
        self.add_eval_ir_byte_allocation_world_laws_v1()?;
        self.add_eval_ir_byte_call_laws_v1()?;
        self.add_eval_ir_byte_initialization_laws_v1()?;
        self.add_eval_ir_byte_binding_laws_v1()?;
        self.add_eval_ir_byte_step_laws_v1()?;
        self.add_eval_ir_byte_overflow_laws_v1()?;
        self.add_eval_ir_byte_range_laws_v1()?;
        self.add_eval_ir_byte_atomic_laws_v1()?;
        self.add_eval_ir_byte_old_frame_laws_v1()?;
        self.add_eval_ir_byte_fresh_separation_laws_v1()?;
        self.add_eval_ir_byte_import_laws_v1()?;
        self.add_eval_ir_byte_run()?;
        self.add_eval_ir_byte_atomic_step_laws_v1()?;
        self.add_eval_ir_byte_usize_laws_v1()?;
        self.add_eval_ir_byte_usize_cmp_laws_v1()?;
        self.add_eval_ir_byte_usize_cmp_step_laws_v1()?;
        self.add_eval_ir_byte_fat_laws_v1()?;
        self.add_eval_ir_byte_builtin_name_v1()?;
        self.add_eval_ir_byte_arc_frame_v1()?;
        self.add_eval_ir_byte_arc_tail_v1()?;
        self.add_eval_ir_byte_enum_laws_v1()?;
        self.add_eval_ir_byte_const_laws_v1()?;
        self.add_eval_ir_byte_field_laws_v1()?;
        self.add_eval_ir_byte_field_set_laws_v1()?;
        self.add_eval_ir_byte_field_get_laws_v1()?;
        self.add_eval_ir_byte_field_preservation_laws_v1()?;
        self.add_eval_ir_byte_ty_eq_laws_v1()?;
        self.add_eval_ir_byte_site_order_v1()?;
        self.add_eval_ir_byte_field_extract_laws_v1()?;
        Ok(())
    }

    pub(super) fn verify_eval_ir_byte_additions_v1(
        &mut self,
        previous: &std::collections::HashSet<String>,
    ) -> Result<(), SpecError> {
        let mut roots = self
            .definitions()
            .iter()
            .filter(|(name, def)| !previous.contains(*name) && def.elaborated_value.is_some())
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        roots.sort();
        for root in roots {
            self.verify_definition(&root)?;
            let name = Name::from_string(&root);
            let axioms = self
                .env()
                .axiom_deps(&name)
                .ok_or_else(|| SpecError::UnknownDefinition(root.clone()))?;
            if !axioms.is_empty() {
                return Err(SpecError::TypeError(format!(
                    "byte-profile root {root} depends on axioms: {axioms:?}"
                )));
            }
            let markers = self
                .env()
                .trust_marker_deps(&name)
                .ok_or_else(|| SpecError::UnknownDefinition(root.clone()))?;
            if !markers.is_empty() {
                return Err(SpecError::TypeError(format!(
                    "byte-profile root {root} depends on trust markers: {markers:?}"
                )));
            }
        }
        Ok(())
    }

    fn add_eval_ir_byte_run(&mut self) -> Result<(), SpecError> {
        for source in [
            r"def ir_byte_halted_v1 (W : Type) (c : IRByteConfigV1 W) : Bool :=
match c with
| IRByteConfigV1.running s w => Bool.false
| IRByteConfigV1.halted o w => Bool.true",
            r"def ir_byte_outcome_v1 (W : Type) (c : IRByteConfigV1 W) : IROutcome :=
match c with
| IRByteConfigV1.running s w => IROutcome.fuel_out
| IRByteConfigV1.halted o w => o",
            r"def ir_byte_final_world_v1 (W : Type) (c : IRByteConfigV1 W) : IRByteWorldV1 W :=
match c with
| IRByteConfigV1.running s w => w
| IRByteConfigV1.halted o w => w",
            r"def ir_byte_run_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (fuel : Nat) (c : IRByteConfigV1 W) : IRByteConfigV1 W :=
ir_drive_v1 (IRByteConfigV1 W) (ir_byte_halted_v1 W) (ir_byte_step_v1 W ctx providers) fuel c",
            r"def ir_byte_run_zero_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (c : IRByteConfigV1 W) : @Eq (IRByteConfigV1 W) (ir_byte_run_v1 W ctx providers 0 c) c :=
ir_drive_zero_v1 (IRByteConfigV1 W) (ir_byte_halted_v1 W) (ir_byte_step_v1 W ctx providers) c",
            r"def ir_byte_run_add_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (b : Nat) (a : Nat) (c : IRByteConfigV1 W) : @Eq (IRByteConfigV1 W) (ir_byte_run_v1 W ctx providers (Nat.add b a) c) (ir_byte_run_v1 W ctx providers b (ir_byte_run_v1 W ctx providers a c)) :=
ir_drive_add_v1 (IRByteConfigV1 W) (ir_byte_halted_v1 W) (ir_byte_step_v1 W ctx providers) b a c",
            r"def ir_byte_run_halted_v1 (W : Type) (ctx : IRByteContextV1) (providers : IRByteProvidersV1 W) (o : IROutcome) (w : IRByteWorldV1 W) (fuel : Nat) : @Eq (IRByteConfigV1 W) (ir_byte_run_v1 W ctx providers fuel (@IRByteConfigV1.halted W o w)) (@IRByteConfigV1.halted W o w) :=
ir_drive_halted_v1 (IRByteConfigV1 W) (ir_byte_halted_v1 W) (ir_byte_step_v1 W ctx providers) (@IRByteConfigV1.halted W o w) (@Eq.refl Bool Bool.true) fuel",
        ] {
            self.add_recursive_def(source, "Whole-configuration byte/world observation and composition via the shared checked fuel driver; no final memory or provider state is discarded.")?;
        }
        Ok(())
    }
}
