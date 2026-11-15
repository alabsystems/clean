// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's replay of a STORED inductive block (`src/lean/Lean/Replay.lean`,
//! v4.30.0-rc2), for the `.olean` re-check lanes.
//!
//! A `.olean` stores an inductive block as separate constants: the types, the
//! constructors and the recursors, each with every field the kernel generated
//! when Lean admitted the block — constructor types, parameter and field
//! counts, and each recursor's type and reduction rules. The re-check lanes
//! register those constants exactly as stored and check only their types, so
//! a forged recursor rule or recursor type, or a forged constructor type, was
//! the reduction and typing the rest of the module was checked against.
//! Measured 2026-09-24 on `.olean`s written with the kernel bypassed: a
//! recursor stored with no minor premises proved `False`, a recursor whose rule
//! for one constructor is the rule for another proved a false equation, and a
//! constructor stored with type `False` proved `False`; `leanchecker` refuses
//! all three.
//!
//! Lean's `replayConstant` never trusts those stored fields. For an
//! `inductInfo` it rebuilds the declaration from the STORED TYPES ALONE — each
//! inductive type, and each constructor's type, in the stored order — and sends
//! one `inductDecl` to the kernel, which re-derives everything else. Constructors
//! and recursors are postponed, and at the end each stored one must be
//! IDENTICAL (`==`, alpha-equivalence ignoring binder annotations) to the one
//! the kernel generated (`checkPostponedConstructors`: "Invalid constructor",
//! "No such constructor"; `checkPostponedRecursors`: "Invalid recursor",
//! "No such recursor").
//!
//! [`Environment::lean_replay_inductive_block`] is that step for one block of
//! an environment in which the block is resident: it rebuilds the declaration
//! from the resident types, admits it with the kernel's own inductive admission
//! (`add_inductive_core`) in a scratch copy from which the block was removed,
//! and compares every generated inductive, constructor and recursor with the
//! resident one, field by field. A difference is a refusal; nothing is ever
//! installed. What the comparison ignores is only what Lean's does or what is
//! Clean's own derived bookkeeping: binder annotations (Lean's `==` ignores
//! them), a recursor's `arg_order` and per-rule `recursive_fields` (Clean
//! recomputes both from the name and the constructor), and the inductive
//! value's `is_large_elim`, which no `.olean` stores (the loader computes it).
//!
//! The inductive value's `is_recursive`, `is_reflexive` and `is_nested` flags
//! ARE compared. Lean's replay never compares them, but it never needs to: it
//! installs the regenerated inductive value in place of the stored one. Clean's
//! replay installs nothing, so every later declaration is checked against the
//! STORED value, and the kernel reads `is_recursive` (structure and unit-like
//! eta, `tc/eta.rs`). Measured 2026-10-22 (`replay_forged/ReplayForgedIsRec`):
//! `inductive FIR | mk : FIR → FIR` stored with `isRec := false` replayed
//! cleanly, and `∀ x : FIR, FIR.mk x.1 = x := fun x => rfl`, which pinned
//! `leanchecker` refuses (`declaration type mismatch`), was admitted through
//! eta. The kernel's admission computes these flags by Lean's block-level rule
//! (`env/inductive_builder.rs`), so a stored flag is compared with the
//! regenerated one exactly.
//!
//! The block's TYPES are also among the names [`Environment::lean_replay_inductive_block`]
//! returns as generated, so a caller can refuse a stored type no replayed block
//! declares (one whose stored `all` names some other block, or nothing), as it
//! refuses a constructor or recursor no replayed block generates.

use std::collections::BTreeSet;

use crate::expr::{BinderData, BinderInfo, Expr, ExprFolder};
use crate::inductive::{
    Constructor, ConstructorVal, InductiveDecl, InductiveType, InductiveVal, RecursorVal,
};
use crate::name::Name;

use super::{Environment, KernelTheory};

/// Why a stored inductive block is not the block Lean's kernel generates from
/// its stored types.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum InductiveReplayMismatch {
    /// The block's stored constants do not even form a declaration (a type of
    /// the block or one of its constructors is not resident).
    #[error("inductive block `{block}` cannot be rebuilt from its stored constants: {detail}")]
    Malformed {
        /// The block's first type.
        block: Name,
        /// What is missing.
        detail: String,
    },
    /// The kernel refuses the declaration rebuilt from the stored types.
    #[error("inductive block `{block}` is refused by the kernel: {error}")]
    Rejected {
        /// The block's first type.
        block: Name,
        /// The kernel's error.
        error: String,
    },
    /// A stored inductive type differs from the one the kernel generated.
    #[error("invalid inductive type {name}: stored {field} differs from the generated one")]
    InvalidInductive {
        /// The inductive type.
        name: Name,
        /// The differing field.
        field: &'static str,
    },
    /// A stored constructor differs from the one the kernel generated
    /// (Lean's replay: `Invalid constructor`).
    #[error("Invalid constructor {name}: stored {field} differs from the generated one (Lean's replay: checkPostponedConstructors)")]
    InvalidConstructor {
        /// The constructor.
        name: Name,
        /// The differing field.
        field: &'static str,
    },
    /// A stored recursor differs from the one the kernel generated (Lean's
    /// replay: `Invalid recursor`).
    #[error("Invalid recursor {name}: stored {field} differs from the generated one (Lean's replay: checkPostponedRecursors)")]
    InvalidRecursor {
        /// The recursor.
        name: Name,
        /// The differing field.
        field: &'static str,
    },
    /// A stored recursor of the block that the kernel does not generate
    /// (Lean's replay: `No such recursor`).
    #[error("No such recursor {name}: the kernel generates no recursor of that name for block `{block}` (Lean's replay: checkPostponedRecursors)")]
    NoSuchRecursor {
        /// The stored recursor.
        name: Name,
        /// The block's first type.
        block: Name,
    },
}

/// Rewrites every binder annotation to one canonical value: Lean's `==` on
/// `Expr` is `Expr.eqv`, alpha-equivalence with binder annotations ignored
/// (`Lean/Expr.lean`), and Clean's `Expr` keeps no binder names.
struct IgnoreBinderInfo;

impl ExprFolder for IgnoreBinderInfo {
    fn fold_pi(&mut self, bd: BinderData, ty: &Expr, body: &Expr) -> Expr {
        let canon = BinderData::new(BinderInfo::Default, bd.mult);
        Expr::pi(canon, self.fold_expr(ty), self.fold_binder_body(body))
    }

    fn fold_lam(&mut self, bd: BinderData, ty: &Expr, body: &Expr) -> Expr {
        let canon = BinderData::new(BinderInfo::Default, bd.mult);
        Expr::lam(canon, self.fold_expr(ty), self.fold_binder_body(body))
    }
}

/// `a == b` as Lean compares two `Expr`s in its replay and import checks:
/// `Expr.eqv`, alpha-equivalence with binder annotations ignored
/// (`Lean/Expr.lean`). Clean's `Expr` keeps no binder names, so this is
/// structural equality up to binder annotations.
#[must_use]
pub fn lean_expr_eqv(a: &Expr, b: &Expr) -> bool {
    a == b || IgnoreBinderInfo.fold_expr(a) == IgnoreBinderInfo.fold_expr(b)
}

fn lean_eqv(a: &Expr, b: &Expr) -> bool {
    lean_expr_eqv(a, b)
}

/// Whether `name` is `<ty>.rec` or a nested auxiliary `<ty>.rec_<n>` of a type
/// of the block.
fn is_block_recursor_name(name: &Name, types: &[Name]) -> bool {
    let rendered = name.to_string();
    types.iter().any(|ty| {
        let prefix = format!("{ty}.rec");
        rendered == prefix
            || rendered
                .strip_prefix(&prefix)
                .and_then(|rest| rest.strip_prefix('_'))
                .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
    })
}

/// A stored block re-admitted by the kernel in a scratch copy
/// ([`Environment::lean_replay_admit_block`]).
pub(crate) struct ReplayedBlock {
    /// The block's first type.
    pub(crate) head: Name,
    /// The declaration rebuilt from the resident types.
    pub(crate) decl: InductiveDecl,
    /// Everything resident but the block, plus the block as the kernel admitted it.
    pub(crate) scratch: Environment,
    /// The block's recursors as they were resident before the replay.
    pub(crate) stored_recursors: Vec<Name>,
    /// The recursor-table entries the admission generated.
    pub(crate) generated_recursors: Vec<Name>,
}

impl Environment {
    /// Replay the stored inductive block whose types are `types` (Lean's
    /// `replayConstant` for an `inductInfo`, then its
    /// `checkPostponedConstructors` / `checkPostponedRecursors` for the
    /// block): rebuild the declaration from the resident types, admit it in a
    /// scratch copy with the block removed, and require every resident
    /// inductive, constructor and recursor of the block to equal the generated
    /// one. `types` may name any member type of the block, or one of its
    /// constructors; the block is the resident `all` list of that type.
    ///
    /// Returns the names of the types, constructors and recursors the kernel
    /// generated for the block: a caller replaying a module refuses any stored
    /// type, constructor or recursor that no block of the module generates
    /// (Lean's replay adds a type only through the `inductDecl` its block
    /// builds, and refuses a constructor or recursor no block generated: "No
    /// such constructor" / "No such recursor").
    ///
    /// The scratch admission runs in Lean's kernel theory: an environment in
    /// [`KernelTheory::Extended`] (the `verify_batch_full` lanes set the theory
    /// on their checkers, not on the environment) is replayed under
    /// [`KernelTheory::Lean`], so the block's universe checks, its recursor's
    /// elimination level and K target follow pinned Lean (DECISIONS R150).
    ///
    /// # Errors
    /// [`InductiveReplayMismatch`] naming the first difference found.
    pub fn lean_replay_inductive_block(
        &self,
        types: &[Name],
    ) -> Result<BTreeSet<Name>, InductiveReplayMismatch> {
        let scratch_theory = match self.kernel_theory() {
            KernelTheory::Extended => Some(KernelTheory::Lean),
            KernelTheory::Lean | KernelTheory::LeanReference => None,
        };
        let replayed = self.lean_replay_admit_block_in(types, scratch_theory)?;
        self.compare_replayed_block(&replayed, false)
    }

    /// The reference entry's re-check of a resident inductive block (KR1,
    /// R161: the gap R143 left open). Like [`Self::lean_replay_inductive_block`],
    /// it re-runs the kernel's whole inductive admission on the block's resident
    /// types in a scratch copy with the block removed — positivity (direct
    /// and nested), constructor shape, the block-agreement and universe
    /// checks, and the well-typedness of every type and constructor — and
    /// compares every resident member with the generated one. Unlike that
    /// replay, which moves an `Extended` environment's scratch to
    /// `KernelTheory::Lean` (R150), this one keeps THIS environment's theory,
    /// mode and settings (`LeanReference` under the reference entry). On top
    /// of that, two fields the `.olean` replay leaves to its loader and the
    /// reference entry reads as they are resident: the inductive value's
    /// `is_large_elim` (which decides whether a `Prop` family eliminates
    /// into `Type`), and each type's constant-table entry (what `infer_type`
    /// reads for the type's name).
    ///
    /// Returns the names of the types, constructors and recursors the kernel
    /// generated for the block; the caller refuses a resident record of the
    /// family that is not among them.
    ///
    /// # Errors
    /// [`InductiveReplayMismatch`] naming the first difference found.
    pub(crate) fn reference_recheck_inductive_block(
        &self,
        member: &Name,
    ) -> Result<BTreeSet<Name>, InductiveReplayMismatch> {
        let replayed = self.lean_replay_admit_block(std::slice::from_ref(member))?;
        let generated = self.compare_replayed_block(&replayed, true)?;
        for ty in &replayed.decl.types {
            let differs = |field| InductiveReplayMismatch::InvalidInductive {
                name: ty.name.clone(),
                field,
            };
            let (Some(stored), Some(built)) = (
                self.get_inductive(&ty.name),
                replayed.scratch.get_inductive(&ty.name),
            ) else {
                return Err(differs("presence"));
            };
            if stored.is_large_elim != built.is_large_elim {
                return Err(differs("large-elimination flag"));
            }
            match self.get_const(&ty.name) {
                Some(ci)
                    if ci.level_params == built.level_params
                        && lean_eqv(&ci.type_, &built.type_)
                        && ci.value.is_none() => {}
                _ => return Err(differs("constant-table entry")),
            }
        }
        Ok(generated)
    }

    /// The reference entry's re-check of a resident auxiliary eliminator
    /// (`<ty>.casesOn` / `<ty>.recOn`, R161 review): the block replay admits
    /// with `GeneratedAuxDefs::Skip`, so these recursor-table entries are not
    /// among the members it generates. Each is compared field by field with
    /// the entry the kernel's own builders generate from the resident family
    /// (`build_cases_on` / `build_rec_on`, as the import tier's
    /// `regenerate_family` runs them), under the reference comparison of
    /// `compare_recursor`. Returns the `<ty>` it belongs to, or
    /// `None` when `name` is not a resident recursor named like one.
    ///
    /// # Errors
    /// Why the resident `<ty>.casesOn` / `<ty>.recOn` is not the kernel's.
    pub(crate) fn reference_recheck_aux_eliminator(
        &self,
        name: &Name,
    ) -> Result<Option<Name>, String> {
        let crate::name::NameInner::Str(parent, suffix) = name.inner() else {
            return Ok(None);
        };
        let suffix: &str = suffix.as_ref();
        let Some(rec) = self.get_recursor(name) else {
            return Ok(None);
        };
        if !matches!(suffix, "casesOn" | "recOn") {
            return Ok(None);
        }
        let root = parent.as_ref().clone();
        let generated = self.regenerate_family(&root)?;
        let Some(built) = generated.iter().find(|g| g.name == *name) else {
            return Err(format!(
                "the kernel generates no recursor of this name for family {root}"
            ));
        };
        // The reference comparison of `compare_recursor` (universe parameters
        // up to renaming, ι-rule lambda domains erased): `with_prelude`'s
        // hand-repaired `Eq.casesOn` / `Eq.recOn` differ from the generated
        // ones exactly as its `Eq.rec` does.
        let renamed;
        let built = if rec.level_params != built.level_params
            && rec.level_params.len() == built.level_params.len()
            && distinct(&rec.level_params)
        {
            renamed = rename_recursor_levels(built, &rec.level_params);
            &renamed
        } else {
            built
        };
        compare_recursor_vals(
            &erase_iota_binder_domains(rec),
            &erase_iota_binder_domains(built),
        )
        .map_err(|field| format!("{field} differs from the generated entry"))?;
        if rec.inductive_name != built.inductive_name {
            return Err("eliminated inductive differs from the generated entry".to_string());
        }
        match self.get_const(name) {
            Some(ci) if ci.level_params == rec.level_params && lean_eqv(&ci.type_, &rec.type_) => {}
            _ => return Err("constant-table entry differs from the recursor".to_string()),
        }
        Ok(Some(root))
    }

    /// The comparison half of [`Self::lean_replay_inductive_block`]. With
    /// `alpha_levels` (the reference entry's re-check), a recursor is
    /// compared up to two differences that change no reduction and no type:
    /// a renaming of its universe parameters (they are binders:
    /// `Eq.rec.{v, u}` and `Eq.rec.{u_1, u}` with the same body are one
    /// recursor), and the domains of each rule's leading params + motives +
    /// minors + fields lambdas, which ι-reduction always applies to exactly
    /// that many arguments (`tc/reduction`, `try_iota_reduction`) and the
    /// rule's subject-reduction check (`authenticate_recursor_readonly`)
    /// types after β. `Environment::with_prelude`'s hand-repaired `Eq.rec`
    /// (`env/core_eq/recursors.rs`) differs from the kernel's in exactly
    /// these two ways (motive universe `v`, placeholder `Prop` binder
    /// domains). The `.olean` replay keeps Lean's exact comparison.
    fn compare_replayed_block(
        &self,
        replayed: &ReplayedBlock,
        alpha_levels: bool,
    ) -> Result<BTreeSet<Name>, InductiveReplayMismatch> {
        let scratch = &replayed.scratch;
        let mut generated: BTreeSet<Name> = BTreeSet::new();
        for ty in &replayed.decl.types {
            self.compare_inductive(scratch, &ty.name)?;
            generated.insert(ty.name.clone());
            for ctor in &ty.constructors {
                self.compare_constructor(scratch, &ctor.name)?;
                generated.insert(ctor.name.clone());
            }
        }
        for rec in &replayed.generated_recursors {
            if self.recursors.contains_key(rec) {
                self.compare_recursor(scratch, rec, alpha_levels)?;
            }
            generated.insert(rec.clone());
        }
        if let Some(extra) = replayed
            .stored_recursors
            .iter()
            .find(|r| !generated.contains(*r))
        {
            return Err(InductiveReplayMismatch::NoSuchRecursor {
                name: extra.clone(),
                block: replayed.head.clone(),
            });
        }
        Ok(generated)
    }

    /// The admission half of [`Self::lean_replay_inductive_block`]: rebuild the
    /// block `types` names from its RESIDENT types and constructor types, and
    /// admit it with the kernel's own `add_inductive_core` in a scratch copy
    /// from which the block was removed. Nothing is compared and nothing is
    /// installed in `self`. Shared with the import tier's nested-family check
    /// (`env/imported_family.rs`), so there is one re-admission, not two.
    ///
    /// # Errors
    /// [`InductiveReplayMismatch::Malformed`] when the block is not resident
    /// with all its constructors; [`InductiveReplayMismatch::Rejected`] when
    /// kernel admission refuses it.
    pub(crate) fn lean_replay_admit_block(
        &self,
        types: &[Name],
    ) -> Result<ReplayedBlock, InductiveReplayMismatch> {
        self.lean_replay_admit_block_in(types, None)
    }

    /// [`Self::lean_replay_admit_block`], with the scratch copy's kernel theory
    /// set to `scratch_theory` when given (`None` keeps this environment's).
    fn lean_replay_admit_block_in(
        &self,
        types: &[Name],
        scratch_theory: Option<KernelTheory>,
    ) -> Result<ReplayedBlock, InductiveReplayMismatch> {
        let first = types.first().cloned().unwrap_or_else(Name::anon);
        // A constructor names its inductive's block too.
        let first = self
            .get_constructor(&first)
            .map_or(first, |cv| cv.inductive_name.clone());
        let block: Vec<Name> = self
            .get_inductive(&first)
            .map(|ind| ind.all_names.clone())
            .filter(|all| !all.is_empty())
            .unwrap_or_else(|| types.to_vec());
        let head = block.first().cloned().unwrap_or_else(Name::anon);
        let malformed = |detail: String| InductiveReplayMismatch::Malformed {
            block: head.clone(),
            detail,
        };
        let Some(head_val) = self.get_inductive(&head) else {
            return Err(malformed(format!(
                "`{head}` is not a resident inductive type"
            )));
        };
        let mut decl_types = Vec::with_capacity(block.len());
        for ty in &block {
            let Some(ind) = self.get_inductive(ty) else {
                return Err(malformed(format!(
                    "`{ty}` is not a resident inductive type"
                )));
            };
            let mut constructors = Vec::with_capacity(ind.constructor_names.len());
            for ctor in &ind.constructor_names {
                let Some(cv) = self.get_constructor(ctor) else {
                    return Err(malformed(format!("constructor `{ctor}` is not resident")));
                };
                constructors.push(Constructor {
                    name: ctor.clone(),
                    type_: cv.type_.clone(),
                });
            }
            decl_types.push(InductiveType {
                name: ty.clone(),
                type_: ind.type_.clone(),
                constructors,
            });
        }
        let decl = InductiveDecl {
            level_params: head_val.level_params.clone(),
            num_params: head_val.num_params,
            types: decl_types,
        };

        // The scratch copy: everything resident but the block itself.
        let mut scratch = self.clone();
        if let Some(theory) = scratch_theory {
            scratch.set_kernel_theory(theory);
        }
        let stored_recursors: Vec<Name> = self
            .recursors
            .keys()
            .filter(|n| is_block_recursor_name(n, &block))
            .cloned()
            .collect();
        for ty in &decl.types {
            scratch.forget_family_member(&ty.name);
            for ctor in &ty.constructors {
                scratch.forget_family_member(&ctor.name);
            }
        }
        for rec in &stored_recursors {
            scratch.forget_family_member(rec);
        }
        let before: BTreeSet<Name> = scratch.recursors.keys().cloned().collect();
        // `add_inductive_core` without its transaction snapshot: a refused
        // block drops the scratch, so nothing would ever read the restore.
        let scratch = scratch
            .into_scratch_with_inductive_core(decl.clone())
            .map_err(|error| InductiveReplayMismatch::Rejected {
                block: head.clone(),
                error: error.to_string(),
            })?;

        let generated_recursors: Vec<Name> = scratch
            .recursors
            .keys()
            .filter(|n| !before.contains(*n))
            .cloned()
            .collect();
        Ok(ReplayedBlock {
            head,
            decl,
            scratch,
            stored_recursors,
            generated_recursors,
        })
    }

    /// Remove a type, constructor or recursor from every table the inductive
    /// admission consults, so the scratch copy can admit the block afresh.
    fn forget_family_member(&mut self, name: &Name) {
        self.constants.remove(name);
        self.declaration_verification.remove(name);
        self.inductives.remove(name);
        self.constructors.remove(name);
        self.recursors.remove(name);
    }

    fn compare_inductive(
        &self,
        generated: &Environment,
        name: &Name,
    ) -> Result<(), InductiveReplayMismatch> {
        let differs = |field| InductiveReplayMismatch::InvalidInductive {
            name: name.clone(),
            field,
        };
        let (Some(stored), Some(built)) = (self.get_inductive(name), generated.get_inductive(name))
        else {
            return Err(differs("presence"));
        };
        compare_inductive_vals(stored, built).map_err(differs)
    }

    fn compare_constructor(
        &self,
        generated: &Environment,
        name: &Name,
    ) -> Result<(), InductiveReplayMismatch> {
        let differs = |field| InductiveReplayMismatch::InvalidConstructor {
            name: name.clone(),
            field,
        };
        let (Some(stored), Some(built)) =
            (self.get_constructor(name), generated.get_constructor(name))
        else {
            return Err(differs("presence"));
        };
        compare_constructor_vals(stored, built).map_err(differs)?;
        // The constant-table mirror is what `infer_type` reads.
        match self.get_const(name) {
            Some(ci) if lean_eqv(&ci.type_, &built.type_) && ci.value.is_none() => Ok(()),
            _ => Err(differs("constant-table entry")),
        }
    }

    fn compare_recursor(
        &self,
        generated: &Environment,
        name: &Name,
        alpha_levels: bool,
    ) -> Result<(), InductiveReplayMismatch> {
        let differs = |field| InductiveReplayMismatch::InvalidRecursor {
            name: name.clone(),
            field,
        };
        let (Some(stored), Some(built)) = (self.get_recursor(name), generated.get_recursor(name))
        else {
            return Err(differs("presence"));
        };
        let renamed;
        let built = if alpha_levels
            && stored.level_params != built.level_params
            && stored.level_params.len() == built.level_params.len()
            && distinct(&stored.level_params)
        {
            renamed = rename_recursor_levels(built, &stored.level_params);
            &renamed
        } else {
            built
        };
        if alpha_levels {
            compare_recursor_vals(
                &erase_iota_binder_domains(stored),
                &erase_iota_binder_domains(built),
            )
            .map_err(differs)?;
        } else {
            compare_recursor_vals(stored, built).map_err(differs)?;
        }
        match self.get_const(name) {
            Some(ci) if lean_eqv(&ci.type_, &built.type_) && ci.value.is_none() => Ok(()),
            _ => Err(differs("constant-table entry")),
        }
    }

    /// Compare one family member as a `.olean` STORES it with the member this
    /// environment holds under the same name, which the caller has had the
    /// kernel generate (`add_inductive_core` over the stored types — the
    /// sequential `stamp-verified` lane replays every block that way before it
    /// checks the module's other declarations). Lean's `checkPostponed*` for
    /// one member: the stored one must equal the generated one field by field.
    ///
    /// # Errors
    /// [`InductiveReplayMismatch`] naming the member and the first differing
    /// field; `presence` when this environment generated no member of that
    /// name ("No such constructor/recursor").
    pub fn lean_replay_compare_stored_member(
        &self,
        stored: StoredFamilyMember<'_>,
    ) -> Result<(), InductiveReplayMismatch> {
        match stored {
            StoredFamilyMember::Inductive(ind) => {
                let differs = |field| InductiveReplayMismatch::InvalidInductive {
                    name: ind.name.clone(),
                    field,
                };
                let built = self.get_inductive(&ind.name).ok_or(differs("presence"))?;
                compare_inductive_vals(ind, built).map_err(differs)
            }
            StoredFamilyMember::Constructor(cv) => {
                let differs = |field| InductiveReplayMismatch::InvalidConstructor {
                    name: cv.name.clone(),
                    field,
                };
                let built = self.get_constructor(&cv.name).ok_or(differs("presence"))?;
                compare_constructor_vals(cv, built).map_err(differs)
            }
            StoredFamilyMember::Recursor(rv) => {
                let differs = |field| InductiveReplayMismatch::InvalidRecursor {
                    name: rv.name.clone(),
                    field,
                };
                let built = self.get_recursor(&rv.name).ok_or(differs("presence"))?;
                compare_recursor_vals(rv, built).map_err(differs)
            }
        }
    }
}

/// One stored inductive-family member, for
/// [`Environment::lean_replay_compare_stored_member`].
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum StoredFamilyMember<'a> {
    /// A stored inductive type.
    Inductive(&'a InductiveVal),
    /// A stored constructor.
    Constructor(&'a ConstructorVal),
    /// A stored recursor.
    Recursor(&'a RecursorVal),
}

/// Whether every name in `names` is different from every other.
fn distinct(names: &[Name]) -> bool {
    let set: BTreeSet<&Name> = names.iter().collect();
    set.len() == names.len()
}

/// `rec` with its universe parameters renamed, position by position, to
/// `to` (simultaneously, in its type and every rule's right-hand side).
fn rename_recursor_levels(rec: &RecursorVal, to: &[Name]) -> RecursorVal {
    let levels: Vec<crate::level::Level> = to
        .iter()
        .map(|n| crate::level::Level::param(n.clone()))
        .collect();
    let mut out = rec.clone();
    out.level_params = to.to_vec();
    out.type_ = rec
        .type_
        .instantiate_level_params_direct(&rec.level_params, &levels);
    for rule in &mut out.rules {
        rule.rhs = rule
            .rhs
            .instantiate_level_params_direct(&rec.level_params, &levels);
    }
    out
}

/// `rec` with the domain of each rule's leading params + motives + minors +
/// fields lambdas replaced by `Prop` (as many of them as are lambdas).
fn erase_iota_binder_domains(rec: &RecursorVal) -> RecursorVal {
    fn erase(e: &Expr, n: usize) -> Expr {
        match (e.kind(), n) {
            (crate::expr::ExprKind::Lam(bd, _, body), n) if n > 0 => {
                Expr::lam(*bd, Expr::prop(), erase(body, n - 1))
            }
            _ => e.clone(),
        }
    }
    let leading = rec.num_params as usize + rec.num_motives as usize + rec.num_minors as usize;
    let mut out = rec.clone();
    for rule in &mut out.rules {
        rule.rhs = erase(&rule.rhs, leading + rule.num_fields as usize);
    }
    out
}

/// Field-by-field equality of two inductive values: the fields Lean's replay
/// rebuilds the declaration from or that decide the block's shape, and the
/// flags its kernel regenerates (`isRec`, `isReflexive`, `numNested > 0`),
/// which Clean's kernel reads from whichever value is resident. Only
/// `is_large_elim`, which no `.olean` stores, is left out.
fn compare_inductive_vals(stored: &InductiveVal, built: &InductiveVal) -> Result<(), &'static str> {
    if stored.level_params != built.level_params {
        return Err("level parameters");
    }
    if !lean_eqv(&stored.type_, &built.type_) {
        return Err("type");
    }
    if stored.num_params != built.num_params {
        return Err("number of parameters");
    }
    if stored.num_indices != built.num_indices {
        return Err("number of indices");
    }
    if stored.all_names != built.all_names {
        return Err("mutual block");
    }
    if stored.constructor_names != built.constructor_names {
        return Err("constructor list");
    }
    if stored.is_recursive != built.is_recursive {
        return Err("recursive flag (isRec)");
    }
    if stored.is_reflexive != built.is_reflexive {
        return Err("reflexive flag (isReflexive)");
    }
    if stored.is_nested != built.is_nested {
        return Err("nested flag (numNested > 0)");
    }
    Ok(())
}

/// Field-by-field equality of two constructors, as Lean's `ConstructorVal`
/// `==` (minus `isUnsafe`, which the loader carries as a separate mark).
fn compare_constructor_vals(
    stored: &ConstructorVal,
    built: &ConstructorVal,
) -> Result<(), &'static str> {
    if stored.level_params != built.level_params {
        return Err("level parameters");
    }
    if !lean_eqv(&stored.type_, &built.type_) {
        return Err("type");
    }
    if stored.inductive_name != built.inductive_name {
        return Err("inductive type");
    }
    if stored.constructor_idx != built.constructor_idx {
        return Err("constructor index");
    }
    if stored.num_params != built.num_params {
        return Err("number of parameters");
    }
    if stored.num_fields != built.num_fields {
        return Err("number of fields");
    }
    Ok(())
}

/// Field-by-field equality of two recursors, as Lean's `RecursorVal` `==`
/// (minus `all` and `isUnsafe`, which Clean does not store on the recursor, and
/// plus nothing Clean derives on its own).
fn compare_recursor_vals(stored: &RecursorVal, built: &RecursorVal) -> Result<(), &'static str> {
    if stored.level_params != built.level_params {
        return Err("level parameters");
    }
    if !lean_eqv(&stored.type_, &built.type_) {
        return Err("type");
    }
    if stored.num_params != built.num_params {
        return Err("number of parameters");
    }
    if stored.num_indices != built.num_indices {
        return Err("number of indices");
    }
    if stored.num_motives != built.num_motives {
        return Err("number of motives");
    }
    if stored.num_minors != built.num_minors {
        return Err("number of minor premises");
    }
    if stored.is_k != built.is_k {
        return Err("K-like flag");
    }
    if stored.rules.len() != built.rules.len() {
        return Err("number of rules");
    }
    for (s, b) in stored.rules.iter().zip(&built.rules) {
        if s.constructor_name != b.constructor_name {
            return Err("rule constructor");
        }
        if s.num_fields != b.num_fields {
            return Err("rule field count");
        }
        if !lean_eqv(&s.rhs, &b.rhs) {
            return Err("rule right-hand side");
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "inductive_lean_replay_tests.rs"]
mod tests;
