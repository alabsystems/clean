// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `deriving Hashable` builders for monomorphic structures and inductives
//! (B98) — replaces the blanket "requires a … hash builder" rejections with
//! real constructor-aware / field-fold instance values.
//!
//! FIDELITY NOTE: real Lean 4 derives `Hashable` over `UInt64` with `mixHash`.
//! Clean's kernel `Hashable` class is **Nat-valued** (`hash : α → Nat`; see
//! `clean-kernel/src/env/data_typeclasses_hashable.rs`, a pre-existing kernel
//! divergence) and the prelude ships no `mixHash`. The derived instances
//! therefore use a documented deterministic Nat mixing formula:
//!
//! ```text
//! hash (Cᵢ f₁ … fₖ) = ((i * 31 + hash f₁) * 31 + hash f₂) * 31 + … + hash fₖ
//! ```
//!
//! i.e. a left fold `mix a b = a * 31 + b` (`Nat.mul` / `Nat.add`) over the
//! per-field hashes, seeded with the constructor's 0-based index `i`. A
//! field-less constructor hashes to exactly its index (so a nullary enum's
//! hash is the constructor ordinal), and a structure is the `i = 0` case of
//! its sole constructor. Each field hashes through its own `[Hashable F]`
//! instance resolved at derive time (Nat/Bool from the prelude, other derived
//! types from their registered derived instances). Derived hash VALUES are
//! Clean-defined behavior, not Lean-compatible values.
//!
//! Descoped shapes stay LOUD (`ElabError::Unsupported`): parametric types,
//! and recursive / nested-container constructor fields (a self-referential
//! `hash` needs the recursor, not `casesOn`).

use super::beq_inductive::CtorFields;
use crate::infer::{DerivedInstance, ElabCtx};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};
use clean_parser::{SurfaceBinder, SurfaceCtor, SurfaceField};

/// `mix acc h = acc * 31 + h` — the documented deterministic Nat combiner
/// (`Nat.mul` / `Nat.add` are prelude kernel constants; both reduce on
/// literals, so enum hashes normalize to `Nat` literals).
fn mix_hash(acc: Expr, field_hash: Expr) -> Expr {
    let shifted = Expr::apps(
        Expr::const_(Name::from_string("Nat.mul"), vec![]),
        [acc, Expr::nat_lit(31)],
    );
    Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [shifted, field_hash],
    )
}

/// Hashable derive implementations (structure + inductive).
impl<'a> ElabCtx<'a> {
    /// Derive `Hashable` for a monomorphic structure.
    ///
    /// ```text
    /// instance : Hashable S where
    ///   hash x := ((0 * 31 + hash x.f₁) * 31 + …) * 31 + hash x.fₖ
    /// ```
    ///
    /// Universe handling mirrors `derive_beq`: `Hashable.{u} : Type u →
    /// Type u`, so a monomorphic `S : Type 0` gets explicit `.{0}` levels.
    /// Parametric structures are descoped LOUD (no silent stub).
    pub(super) fn derive_hashable(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
    ) -> Result<DerivedInstance, ElabError> {
        if !binders.is_empty() {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "deriving Hashable for `{struct_name}` does not yet support parametric structures"
                ),
            });
        }

        let hash_u = Level::zero();
        let struct_type = Expr::const_(struct_name.clone(), vec![]);
        let instance_ty = Expr::app(
            Expr::const_(Name::from_string("Hashable"), vec![hash_u.clone()]),
            struct_type.clone(),
        );

        // `fun (x : S) => <fold>` — x = bvar 0; fields via kernel projections.
        let x_ref = Expr::bvar(0);
        let mut acc = Expr::nat_lit(0);
        for (idx, field) in fields.iter().enumerate() {
            // SAFETY: field index bounded by the structure's field count.
            let idx_u32 = u32::try_from(idx).unwrap_or(u32::MAX);
            let x_field = Expr::proj(struct_name.clone(), idx_u32, x_ref.clone());
            let field_ty = self.elaborate(&field.ty)?;
            let field_hash =
                self.build_field_hash_call(struct_name, &field.name, &field_ty, x_field)?;
            acc = mix_hash(acc, field_hash);
        }
        let hash_fn = Expr::lam(BinderInfo::Default, struct_type.clone(), acc);

        // `@Hashable.mk.{0} S hash_fn` — the implicit `α` must be supplied
        // explicitly (the value is committed to the kernel verbatim).
        let instance_val = Expr::apps(
            Expr::const_(Name::from_string("Hashable.mk"), vec![hash_u]),
            [struct_type, hash_fn],
        );

        Ok(DerivedInstance {
            name: Name::from_string(&format!("inst{struct_name}Hashable")),
            class_name: Name::from_string("Hashable"),
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// Derive `Hashable` for a monomorphic inductive whose constructor fields
    /// are all non-recursive with closed `[Hashable F]` instances (nullary
    /// enums are the field-less special case):
    ///
    /// ```text
    /// instance : Hashable T where
    ///   hash x := T.casesOn.{1} (fun _ => Nat) x
    ///     (fun (f₁ : F₀₁) … => ((0 * 31 + hash f₁) * 31 + …))   -- ctor 0
    ///     …
    ///     (fun … => ((i * 31 + hash f₁) * 31 + …))              -- ctor i
    /// ```
    ///
    /// Parametric, recursive, and nested-container shapes are descoped LOUD.
    pub(super) fn derive_hashable_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        ctors: &[SurfaceCtor],
        ctor_names: &[Name],
    ) -> Result<DerivedInstance, ElabError> {
        if !binders.is_empty() {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "deriving Hashable for `{ind_name}` does not yet support parametric inductives"
                ),
            });
        }

        // Per-ctor elaborated field types; recursive / nested-container fields
        // (which mention the inductive itself) and unresolvable-instance fields
        // fail the gate and descope LOUD below.
        let ctor_fields = self
            .collect_ctor_fields(ind_name, ctors)
            .filter(|cf| cf.iter().all(|c| !c.has_recursive_field))
            .filter(|cf| self.all_field_hashable_instances_closed(cf))
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!(
                    "deriving Hashable for `{ind_name}` requires a closed structural hash for \
                     every constructor field; recursive and nested-container shapes are not \
                     yet supported"
                ),
            })?;

        let hash_u = Level::zero();
        let ind_type = Expr::const_(ind_name.clone(), vec![]);
        let instance_ty = Expr::app(
            Expr::const_(Name::from_string("Hashable"), vec![hash_u.clone()]),
            ind_type.clone(),
        );

        // `T.casesOn.{1} (fun _ : T => Nat) x minor…` — motive returns
        // `Nat : Sort 1`; Lean-faithful casesOn order: motive, major, minors.
        let motive_u = Level::succ(Level::zero());
        let cases_on_name = Name::from_string(&format!("{ind_name}.casesOn"));
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let motive = Expr::lam(BinderInfo::Default, ind_type.clone(), nat_ty);

        let mut minors = Vec::with_capacity(ctor_fields.len());
        for (i, cf) in ctor_fields.iter().enumerate() {
            let fvars: Vec<FVarId> = cf.field_types.iter().map(|_| self.fresh_fvar()).collect();
            // Seed with the ctor ordinal, then fold the field hashes.
            let mut minor = Expr::nat_lit(i as u64);
            for (k, fty) in cf.field_types.iter().enumerate() {
                let field_hash = self.build_field_hash_call(
                    ind_name,
                    &ctor_names[i].to_string(),
                    fty,
                    Expr::fvar(fvars[k]),
                )?;
                minor = mix_hash(minor, field_hash);
            }
            // λ (f : F) … => minor  (abstract innermost-first).
            for k in (0..fvars.len()).rev() {
                minor = minor.abstract_fvar(fvars[k]);
                minor = Expr::lam(BinderInfo::Default, cf.field_types[k].clone(), minor);
            }
            minors.push(minor);
        }

        let mut body = Expr::app(Expr::const_(cases_on_name, vec![motive_u]), motive);
        body = Expr::app(body, Expr::bvar(0)); // x as major
        for minor in minors {
            body = Expr::app(body, minor);
        }
        let hash_fn = Expr::lam(BinderInfo::Default, ind_type.clone(), body);

        let instance_val = Expr::apps(
            Expr::const_(Name::from_string("Hashable.mk"), vec![hash_u]),
            [ind_type, hash_fn],
        );

        Ok(DerivedInstance {
            name: Name::from_string(&format!("inst{ind_name}Hashable")),
            class_name: Name::from_string("Hashable"),
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// `@Hashable.hash.{0} F inst value : Nat` — the implicit `{α}` and the
    /// `[Hashable F]` instance are supplied explicitly (the derived value is
    /// committed to the kernel verbatim; mirrors `build_field_beq`). A missing
    /// field instance is a typed derive error, never a leaked metavariable.
    fn build_field_hash_call(
        &mut self,
        owner_name: &Name,
        field_label: &str,
        field_ty: &Expr,
        value: Expr,
    ) -> Result<Expr, ElabError> {
        let hashable_class = Name::from_string("Hashable");
        let goal = Expr::app(self.mk_const(&hashable_class), field_ty.clone());
        let field_inst = self
            .resolve_instance(&goal)
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!(
                    "deriving Hashable for `{owner_name}` cannot synthesize Hashable for \
                     field `{field_label}`"
                ),
            })?;
        let hash_const = Expr::const_(Name::from_string("Hashable.hash"), vec![Level::zero()]);
        Ok(Expr::apps(
            hash_const,
            [field_ty.clone(), field_inst, value],
        ))
    }

    /// Every field's `[Hashable fieldTy]` instance resolves to a CLOSED term
    /// (no fvars / metavariables) — gate for the inductive field-fold path,
    /// mirroring `all_field_ord_instances_closed`.
    fn all_field_hashable_instances_closed(&mut self, ctor_fields: &[CtorFields]) -> bool {
        let hashable_class = Name::from_string("Hashable");
        for cf in ctor_fields {
            for fty in &cf.field_types {
                let goal = Expr::app(self.mk_const(&hashable_class), fty.clone());
                match self.resolve_instance(&goal) {
                    Some(inst) if !inst.has_fvar_quick() && !self.has_metavars(&inst) => {}
                    _ => return false,
                }
            }
        }
        true
    }
}
