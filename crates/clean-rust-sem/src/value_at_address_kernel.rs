// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # Kernel reflection of the value-at-address semantics (M2.4, first brick)
//!
//! M2.4 reflects the executable [`crate::value_at_address`] model into
//! `clean_kernel` as **admitted declarations**, so the M3 refinement proof can
//! reason about it (see `designs/2026-06-29-giveback-clean-refinement.md` §10).
//!
//! This module is the *first brick*: it admits the leaf inductive
//! `RustSem.BorrowPermission` — the kernel image of
//! [`crate::stacked_borrows::BorrowPermission`] — and proves the
//! `clean-rust-sem → add_inductive → axiom-gate` pipeline end-to-end before the
//! full dependency tree (ids, `Place`, `MemOp`, `Config`, `step`) is built out.
//!
//! Per §10's decision, the inductive declarations live here in `clean-rust-sem`
//! (not the kernel crate): `Environment::add_inductive` and every `Expr`
//! constructor are `pub`, so no kernel-private `EnvDeclBuilder` is needed for
//! plain inductives. Admission goes through the type-checked path, so the new
//! constants are axiom-clean (`soundness_report().total_domain_axioms == 0`).

use clean_kernel::{
    BinderInfo, Constructor, Declaration, EnvError, Environment, Expr, InductiveDecl,
    InductiveType, Level, Name,
};

/// Fully-qualified name of the reflected borrow-permission inductive.
pub const BORROW_PERMISSION: &str = "RustSem.BorrowPermission";

/// The four borrow permissions, mirroring
/// [`crate::stacked_borrows::BorrowPermission`] (Unique / SharedReadWrite /
/// SharedReadOnly / Disabled). Constructor suffix in declaration order.
const BORROW_PERMISSION_CTORS: [&str; 4] =
    ["unique", "sharedReadWrite", "sharedReadOnly", "disabled"];

/// Admit `RustSem.BorrowPermission` into `env`.
///
/// A flat four-constructor inductive in `Type` (`Sort 1`), the kernel image of
/// [`crate::stacked_borrows::BorrowPermission`]. Pure inductive — introduces no
/// axioms, so the resulting environment stays axiom-clean. Idempotent only in
/// the sense that re-admitting a duplicate name is an `EnvError::DuplicateName`;
/// callers admitting into a shared env should guard with [`Environment::get_inductive`].
///
/// # Errors
/// Returns the kernel's [`EnvError`] if admission fails (e.g. a name collision).
pub fn declare_borrow_permission(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string(BORROW_PERMISSION);
    // `RustSem.BorrowPermission : Type` (= `Sort 1`), exactly as `Nat : Type`.
    let ty = Expr::sort(Level::succ(Level::zero()));
    let self_const = Expr::const_(name.clone(), vec![]);
    let constructors = BORROW_PERMISSION_CTORS
        .iter()
        .map(|suffix| Constructor {
            name: Name::from_string(format!("{BORROW_PERMISSION}.{suffix}").as_str()),
            // Nullary constructor: `RustSem.BorrowPermission.unique : RustSem.BorrowPermission`.
            type_: self_const.clone(),
        })
        .collect();
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name,
            type_: ty,
            constructors,
        }],
    };
    env.add_inductive(decl)
}

/// Fully-qualified name of the reflected `AllocId` (heap-block id) newtype.
pub const ALLOC_ID: &str = "RustSem.AllocId";
/// Fully-qualified name of the reflected `BorrowTag` newtype.
pub const BORROW_TAG: &str = "RustSem.BorrowTag";
/// Fully-qualified name of the reflected `ProtectorId` newtype.
pub const PROTECTOR_ID: &str = "RustSem.ProtectorId";

/// Admit a single-constructor `Nat`-wrapping newtype inductive `type_name` with
/// constructor `type_name.mk : Nat → type_name`.
///
/// Mirrors the executable id newtypes (each a transparent index over the
/// naturals). **Precondition:** `Nat` must already be admitted (call
/// [`Environment::init_nat`]) — the constructor type references it.
///
/// # Errors
/// Returns [`EnvError`] if admission fails (e.g. `Nat` absent, or a name clash).
fn declare_nat_newtype(env: &mut Environment, type_name: &str) -> Result<(), EnvError> {
    let name = Name::from_string(type_name);
    let ty = Expr::sort(Level::succ(Level::zero()));
    let self_const = Expr::const_(name.clone(), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // `type_name.mk : Nat → type_name`
    let ctor = Constructor {
        name: Name::from_string(format!("{type_name}.mk").as_str()),
        type_: Expr::arrow(nat, self_const),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name,
            type_: ty,
            constructors: vec![ctor],
        }],
    };
    env.add_inductive(decl)
}

/// Admit the value-at-address id newtypes (`AllocId`, `BorrowTag`,
/// `ProtectorId`), each a `Nat`-wrapping single-constructor inductive.
///
/// **Precondition:** `Nat` is admitted (see [`declare_nat_newtype`]). Pure
/// inductives — introduce no axioms.
///
/// # Errors
/// Returns [`EnvError`] on the first admission failure.
pub fn declare_id_newtypes(env: &mut Environment) -> Result<(), EnvError> {
    declare_nat_newtype(env, ALLOC_ID)?;
    declare_nat_newtype(env, BORROW_TAG)?;
    declare_nat_newtype(env, PROTECTOR_ID)?;
    Ok(())
}

/// Fully-qualified name of the reflected `Place` inductive.
pub const PLACE: &str = "RustSem.Place";

/// Admit `RustSem.Place` — the recursive kernel image of
/// [`crate::ownership::Place`].
///
/// Constructors (all strictly positive, so the kernel's positivity check
/// passes): `local : Nat → Place`, `static : String → Place`,
/// `field : Place → String → Place`, `index : Place → Place → Place`,
/// `deref : Place → Place`, `downcast : Place → String → Place`.
///
/// **Precondition:** `Nat` and `String` are admitted (`init_nat` + `init_string`).
///
/// # Errors
/// Returns [`EnvError`] if admission fails (missing deps, positivity, or clash).
pub fn declare_place(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string(PLACE);
    let ty = Expr::sort(Level::succ(Level::zero()));
    let place = Expr::const_(name.clone(), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let string = Expr::const_(Name::from_string("String"), vec![]);
    let ctor = |suffix: &str, type_: Expr| Constructor {
        name: Name::from_string(format!("{PLACE}.{suffix}").as_str()),
        type_,
    };
    let constructors = vec![
        ctor("local", Expr::arrow(nat.clone(), place.clone())),
        ctor("static", Expr::arrow(string.clone(), place.clone())),
        ctor(
            "field",
            Expr::arrow(place.clone(), Expr::arrow(string.clone(), place.clone())),
        ),
        ctor(
            "index",
            Expr::arrow(place.clone(), Expr::arrow(place.clone(), place.clone())),
        ),
        ctor("deref", Expr::arrow(place.clone(), place.clone())),
        ctor(
            "downcast",
            Expr::arrow(place.clone(), Expr::arrow(string.clone(), place.clone())),
        ),
    ];
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name,
            type_: ty,
            constructors,
        }],
    };
    env.add_inductive(decl)
}

/// Build a curried constructor type `args[0] → args[1] → … → result`.
fn ctor_type(args: &[Expr], result: &Expr) -> Expr {
    args.iter()
        .rev()
        .fold(result.clone(), |acc, arg| Expr::arrow(arg.clone(), acc))
}

/// `List UInt8` — the kernel image of `Vec<u8>` (`Allocation::data`).
fn bytes_ty() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::const_(Name::from_string("UInt8"), vec![]),
    )
}

/// Fully-qualified name of the reflected `MemOp` inductive.
pub const MEM_OP: &str = "RustSem.MemOp";

/// Admit `RustSem.MemOp` — the kernel image of [`crate::value_at_address::MemOp`]
/// (Alloc/Dealloc/Read/Write/Retag).
///
/// **Precondition:** `Nat`, `String`, `List`, `Option`, `UInt8` and the
/// `RustSem.{Place,BorrowPermission,ProtectorId}` declarations are admitted.
/// Sizes/offsets (executable `usize`/`u64`) are abstracted to `Nat`; `data` to
/// `List UInt8`; the retag protector to `Option ProtectorId` (level 0, all
/// referenced types live in `Type 0`).
///
/// # Errors
/// Returns [`EnvError`] if admission fails (missing deps, universe, or clash).
pub fn declare_mem_op(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string(MEM_OP);
    let ty = Expr::sort(Level::succ(Level::zero()));
    let memop = Expr::const_(name.clone(), vec![]);
    let place = Expr::const_(Name::from_string(PLACE), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bperm = Expr::const_(Name::from_string(BORROW_PERMISSION), vec![]);
    let protid = Expr::const_(Name::from_string(PROTECTOR_ID), vec![]);
    let opt_protid = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        protid,
    );
    let bytes = bytes_ty();
    let ctor = |suffix: &str, args: &[Expr]| Constructor {
        name: Name::from_string(format!("{MEM_OP}.{suffix}").as_str()),
        type_: ctor_type(args, &memop),
    };
    let constructors = vec![
        ctor("alloc", &[place.clone(), nat.clone(), nat.clone()]),
        ctor("dealloc", std::slice::from_ref(&place)),
        ctor("read", &[place.clone(), nat.clone(), nat.clone()]),
        ctor("write", &[place.clone(), nat.clone(), bytes]),
        ctor("retag", &[place.clone(), bperm, opt_protid]),
    ];
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name,
            type_: ty,
            constructors,
        }],
    };
    env.add_inductive(decl)
}

/// Fully-qualified name of the reflected `Observation` inductive.
pub const OBSERVATION: &str = "RustSem.Observation";

/// Admit `RustSem.Observation` — the kernel image of
/// [`crate::value_at_address::Observation`]
/// (Allocated/Deallocated/Read/Wrote/Retagged).
///
/// **Precondition:** `List`, `UInt8` and `RustSem.{AllocId,BorrowTag}` admitted.
///
/// # Errors
/// Returns [`EnvError`] if admission fails.
pub fn declare_observation(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string(OBSERVATION);
    let ty = Expr::sort(Level::succ(Level::zero()));
    let obs = Expr::const_(name.clone(), vec![]);
    let alloc_id = Expr::const_(Name::from_string(ALLOC_ID), vec![]);
    let borrow_tag = Expr::const_(Name::from_string(BORROW_TAG), vec![]);
    let bytes = bytes_ty();
    let ctor = |suffix: &str, args: &[Expr]| Constructor {
        name: Name::from_string(format!("{OBSERVATION}.{suffix}").as_str()),
        type_: ctor_type(args, &obs),
    };
    let constructors = vec![
        ctor("allocated", &[alloc_id]),
        ctor("deallocated", &[]),
        ctor("read", &[bytes]),
        ctor("wrote", &[]),
        ctor("retagged", &[borrow_tag]),
    ];
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name,
            type_: ty,
            constructors,
        }],
    };
    env.add_inductive(decl)
}

/// Fully-qualified name of the reflected `StuckReason` inductive.
pub const STUCK_REASON: &str = "RustSem.StuckReason";

/// Admit `RustSem.StuckReason` — the kernel image of
/// [`crate::value_at_address::StuckReason`], the fail-closed rejection reasons
/// (a stuck configuration is the absence of a successor; this enumerates *why*).
///
/// Offsets/sizes (executable `u64`/`usize`) are abstracted to `Nat`; ids are the
/// reflected `RustSem.{AllocId,BorrowTag}`.
///
/// **Precondition:** `Nat` and `RustSem.{AllocId,BorrowTag}` admitted.
///
/// # Errors
/// Returns [`EnvError`] if admission fails.
pub fn declare_stuck_reason(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string(STUCK_REASON);
    let ty = Expr::sort(Level::succ(Level::zero()));
    let stuck = Expr::const_(name.clone(), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let alloc_id = Expr::const_(Name::from_string(ALLOC_ID), vec![]);
    let tag = Expr::const_(Name::from_string(BORROW_TAG), vec![]);
    let ctor = |suffix: &str, args: &[Expr]| Constructor {
        name: Name::from_string(format!("{STUCK_REASON}.{suffix}").as_str()),
        type_: ctor_type(args, &stuck),
    };
    let constructors = vec![
        ctor("nullPointer", &[]),
        ctor("invalidPointer", std::slice::from_ref(&alloc_id)),
        ctor("useAfterFree", std::slice::from_ref(&alloc_id)),
        ctor("doubleFree", std::slice::from_ref(&alloc_id)),
        ctor("outOfBounds", &[nat.clone(), nat.clone(), nat.clone()]),
        ctor("misaligned", &[nat.clone(), nat.clone()]),
        ctor("taintedRead", std::slice::from_ref(&alloc_id)),
        ctor("pointerOverflow", &[]),
        ctor("allocationFailed", &[nat.clone(), nat.clone()]),
        ctor("protectedConflict", &[tag.clone(), tag.clone()]),
        ctor("incompatibleAccess", std::slice::from_ref(&tag)),
        ctor("unknownBorrowTag", std::slice::from_ref(&tag)),
        ctor("missingBorrowParent", std::slice::from_ref(&tag)),
        ctor("unknownBorrowLocation", &[]),
        ctor("unboundPlace", &[]),
        ctor("placeAlreadyBound", &[]),
        ctor("unclassifiedRejection", &[]),
    ];
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name,
            type_: ty,
            constructors,
        }],
    };
    env.add_inductive(decl)
}

/// `List elem` at universe level 0 (all `RustSem.*` types live in `Type 0`).
fn list_of(elem: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        elem.clone(),
    )
}

/// `Option elem` at universe level 0.
fn option_of(elem: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Option"), vec![Level::zero()]),
        elem.clone(),
    )
}

/// Admit a single-constructor "structure" inductive `type_name` in `Type` with
/// constructor `type_name.mk : field_tys[0] → … → type_name`.
fn declare_struct(
    env: &mut Environment,
    type_name: &str,
    field_tys: &[Expr],
) -> Result<(), EnvError> {
    let name = Name::from_string(type_name);
    let ty = Expr::sort(Level::succ(Level::zero()));
    let self_const = Expr::const_(name.clone(), vec![]);
    let ctor = Constructor {
        name: Name::from_string(format!("{type_name}.mk").as_str()),
        type_: ctor_type(field_tys, &self_const),
    };
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name,
            type_: ty,
            constructors: vec![ctor],
        }],
    })
}

/// Fully-qualified names of the reflected `Config` state tower.
pub const ALLOCATION: &str = "RustSem.Allocation";
pub const MEM_ENTRY: &str = "RustSem.MemEntry";
pub const MEMORY: &str = "RustSem.Memory";
pub const BORROW_STACK_ENTRY: &str = "RustSem.BorrowStackEntry";
pub const BORROW_LOC_ENTRY: &str = "RustSem.BorrowLocEntry";
pub const STACKED_BORROWS: &str = "RustSem.StackedBorrows";
pub const BRIDGE_ALLOC_ENTRY: &str = "RustSem.BridgeAllocEntry";
pub const BRIDGE_TAG_ENTRY: &str = "RustSem.BridgeTagEntry";
pub const BRIDGE: &str = "RustSem.Bridge";
pub const CONFIG: &str = "RustSem.Config";

/// Admit the `Config` state tower — the kernel image of
/// [`crate::value_at_address::Config`]. The executable `HashMap`s are modelled
/// as **association lists** keyed by dedicated entry structures (design §10),
/// avoiding any need for a kernel finite-map type:
///
/// - `Allocation { id, size, align, valid, tainted, data:List UInt8 }`
///   (executable `ty?`/`slice_len?` elided for this first Config model);
/// - `Memory { allocations:List MemEntry, next_alloc_id }`, `MemEntry{AllocId,Allocation}`;
/// - `BorrowStackEntry { tag, permission, protector:Option ProtectorId, parent:Option BorrowTag }`,
///   `StackedBorrows { locations:List BorrowLocEntry, next_tag, next_protector }`,
///   `BorrowLocEntry { Place, stack:List BorrowStackEntry }`;
/// - `Bridge { place_to_alloc:List BridgeAllocEntry, current_tag:List BridgeTagEntry }`;
/// - `Config { memory, borrows, bridge }`.
///
/// **Precondition:** `Nat`, `Bool`, `List`, `Option`, `UInt8` and the
/// `RustSem.{AllocId,BorrowTag,ProtectorId,BorrowPermission,Place}` decls admitted.
///
/// # Errors
/// Returns [`EnvError`] on the first admission failure.
pub fn declare_config(env: &mut Environment) -> Result<(), EnvError> {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let boolean = Expr::const_(Name::from_string("Bool"), vec![]);
    let alloc_id = Expr::const_(Name::from_string(ALLOC_ID), vec![]);
    let borrow_tag = Expr::const_(Name::from_string(BORROW_TAG), vec![]);
    let protector_id = Expr::const_(Name::from_string(PROTECTOR_ID), vec![]);
    let bperm = Expr::const_(Name::from_string(BORROW_PERMISSION), vec![]);
    let place = Expr::const_(Name::from_string(PLACE), vec![]);

    // memory layer
    declare_struct(
        env,
        ALLOCATION,
        &[
            alloc_id.clone(),
            nat.clone(),
            nat.clone(),
            boolean.clone(),
            boolean.clone(),
            bytes_ty(),
        ],
    )?;
    let allocation = Expr::const_(Name::from_string(ALLOCATION), vec![]);
    declare_struct(env, MEM_ENTRY, &[alloc_id.clone(), allocation])?;
    let mem_entry = Expr::const_(Name::from_string(MEM_ENTRY), vec![]);
    declare_struct(env, MEMORY, &[list_of(&mem_entry), nat.clone()])?;

    // borrow layer
    declare_struct(
        env,
        BORROW_STACK_ENTRY,
        &[
            borrow_tag.clone(),
            bperm,
            option_of(&protector_id),
            option_of(&borrow_tag),
        ],
    )?;
    let bse = Expr::const_(Name::from_string(BORROW_STACK_ENTRY), vec![]);
    declare_struct(env, BORROW_LOC_ENTRY, &[place.clone(), list_of(&bse)])?;
    let ble = Expr::const_(Name::from_string(BORROW_LOC_ENTRY), vec![]);
    declare_struct(env, STACKED_BORROWS, &[list_of(&ble), nat.clone(), nat])?;

    // bridge layer
    declare_struct(env, BRIDGE_ALLOC_ENTRY, &[place.clone(), alloc_id])?;
    let bae = Expr::const_(Name::from_string(BRIDGE_ALLOC_ENTRY), vec![]);
    declare_struct(env, BRIDGE_TAG_ENTRY, &[place, borrow_tag])?;
    let bte = Expr::const_(Name::from_string(BRIDGE_TAG_ENTRY), vec![]);
    declare_struct(env, BRIDGE, &[list_of(&bae), list_of(&bte)])?;

    // top
    let memory = Expr::const_(Name::from_string(MEMORY), vec![]);
    let stacked = Expr::const_(Name::from_string(STACKED_BORROWS), vec![]);
    let bridge = Expr::const_(Name::from_string(BRIDGE), vec![]);
    declare_struct(env, CONFIG, &[memory, stacked, bridge])?;
    Ok(())
}

/// Fully-qualified name of the reflected `StepOutcome` inductive.
pub const STEP_OUTCOME: &str = "RustSem.StepOutcome";

/// Admit `RustSem.StepOutcome` — the kernel image of
/// [`crate::value_at_address::StepOutcome`]: `stepped : Config → Observation →
/// StepOutcome` (a successor + its observation) or `stuck : StuckReason →
/// StepOutcome` (no successor).
///
/// **Precondition:** `RustSem.{Config,Observation,StuckReason}` admitted.
///
/// # Errors
/// Returns [`EnvError`] if admission fails.
pub fn declare_step_outcome(env: &mut Environment) -> Result<(), EnvError> {
    let name = Name::from_string(STEP_OUTCOME);
    let ty = Expr::sort(Level::succ(Level::zero()));
    let outcome = Expr::const_(name.clone(), vec![]);
    let config = Expr::const_(Name::from_string(CONFIG), vec![]);
    let observation = Expr::const_(Name::from_string(OBSERVATION), vec![]);
    let stuck = Expr::const_(Name::from_string(STUCK_REASON), vec![]);
    let ctor = |suffix: &str, args: &[Expr]| Constructor {
        name: Name::from_string(format!("{STEP_OUTCOME}.{suffix}").as_str()),
        type_: ctor_type(args, &outcome),
    };
    let constructors = vec![
        ctor("stepped", &[config, observation]),
        ctor("stuck", std::slice::from_ref(&stuck)),
    ];
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name,
            type_: ty,
            constructors,
        }],
    })
}

/// Fully-qualified name of the reflected `isStuck` predicate.
pub const IS_STUCK: &str = "RustSem.StepOutcome.isStuck";

/// Admit `RustSem.StepOutcome.isStuck : StepOutcome → Bool`, the kernel image of
/// [`crate::value_at_address::StepOutcome::is_stuck`], as a **recursor-based
/// `Definition`** (not just an inductive). Defined via the auto-derived
/// `RustSem.StepOutcome.rec` with a constant `Bool` motive:
/// `isStuck := λ t => StepOutcome.rec (λ _ => Bool) (λ _ _ => false) (λ _ => true) t`.
///
/// Admitted through the type-checked [`Environment::add_decl`] path, so a buggy
/// term fails to admit rather than slipping through — and it introduces no
/// domain axioms. This proves the function-definition path over the reflected
/// types works axiom-clean, the capability `step` and the §3.5 lemmas need.
///
/// **Precondition:** `Bool` (prelude) and `RustSem.StepOutcome` (with its
/// dependencies) admitted.
///
/// # Errors
/// Returns [`EnvError`] if the definition fails to type-check or admit.
pub fn declare_is_stuck(env: &mut Environment) -> Result<(), EnvError> {
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let true_c = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let false_c = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let outcome = Expr::const_(Name::from_string(STEP_OUTCOME), vec![]);
    let config = Expr::const_(Name::from_string(CONFIG), vec![]);
    let observation = Expr::const_(Name::from_string(OBSERVATION), vec![]);
    let stuck_reason = Expr::const_(Name::from_string(STUCK_REASON), vec![]);

    // motive : StepOutcome → Sort 1  ≡  λ _:StepOutcome => Bool
    let motive = Expr::lam(BinderInfo::Default, outcome.clone(), bool_c.clone());
    // stepped case: λ _:Config => λ _:Observation => Bool.false
    let case_stepped = Expr::lam(
        BinderInfo::Default,
        config,
        Expr::lam(BinderInfo::Default, observation, false_c),
    );
    // stuck case: λ _:StuckReason => Bool.true
    let case_stuck = Expr::lam(BinderInfo::Default, stuck_reason, true_c);
    // StepOutcome.rec.{1} motive case_stepped case_stuck (bvar 0)
    let rec = Expr::const_(
        Name::from_string("RustSem.StepOutcome.rec"),
        vec![Level::succ(Level::zero())],
    );
    let body = Expr::apps(rec, [motive, case_stepped, case_stuck, Expr::bvar(0)]);
    let value = Expr::lam(BinderInfo::Default, outcome.clone(), body);
    let type_ = Expr::arrow(outcome, bool_c);

    env.add_decl(Declaration::Definition {
        name: Name::from_string(IS_STUCK),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
}

/// Name of the computation lemma `isStuck (stuck r) = true`.
pub const IS_STUCK_STUCK_THM: &str = "RustSem.StepOutcome.isStuck_stuck";

/// Admit `∀ r, isStuck (StepOutcome.stuck r) = true` as a kernel `Theorem`,
/// proved by `Eq.refl`: the kernel reduces `isStuck (stuck r)` to `Bool.true`
/// by δ-unfolding `isStuck` and ι-reducing `RustSem.StepOutcome.rec`.
///
/// This exercises the THEOREM path end-to-end — state a `Prop` over the
/// reflected semantics, prove it, admit it axiom-clean (its only axiom is the
/// foundational `Eq.refl`) — and demonstrates the kernel genuinely *computes*
/// with the reflected `step` machinery. It is the last capability the four §3.5
/// metatheory lemmas need (once the full `step` is defined, those lemmas are
/// the same shape at larger scale).
///
/// **Precondition:** `Eq`, `Bool`, and `RustSem.StepOutcome.isStuck` admitted.
///
/// # Errors
/// Returns [`EnvError`] if the proof fails to type-check (the reduction does not
/// hold) or admission fails.
pub fn declare_is_stuck_stuck_lemma(env: &mut Environment) -> Result<(), EnvError> {
    let one = Level::succ(Level::zero());
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let true_c = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let stuck_reason = Expr::const_(Name::from_string(STUCK_REASON), vec![]);
    let is_stuck = Expr::const_(Name::from_string(IS_STUCK), vec![]);
    let stuck_ctor = Expr::const_(Name::from_string("RustSem.StepOutcome.stuck"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);

    // lhs = isStuck (StepOutcome.stuck (bvar 0))   [bvar 0 = r, bound by the ∀]
    let lhs = Expr::app(is_stuck, Expr::app(stuck_ctor, Expr::bvar(0)));
    // Eq Bool (isStuck (stuck r)) Bool.true
    let eq_body = Expr::apps(eq, [bool_c.clone(), lhs, true_c.clone()]);
    // ∀ r : StuckReason, Eq Bool (isStuck (stuck r)) true
    let stmt = Expr::pi(BinderInfo::Default, stuck_reason.clone(), eq_body);
    // λ r : StuckReason => Eq.refl Bool Bool.true   (well-typed up to defeq)
    let refl_app = Expr::apps(eq_refl, [bool_c, true_c]);
    let proof = Expr::lam(BinderInfo::Default, stuck_reason, refl_app);

    env.add_decl(Declaration::Theorem {
        name: Name::from_string(IS_STUCK_STUCK_THM),
        level_params: vec![],
        type_: stmt,
        value: proof,
    })
}

/// Name of the complement computation lemma `isStuck (stepped cfg obs) = false`.
pub const IS_STUCK_STEPPED_THM: &str = "RustSem.StepOutcome.isStuck_stepped";

/// Admit `∀ cfg obs, isStuck (StepOutcome.stepped cfg obs) = false` as a kernel
/// `Theorem`, proved by `Eq.refl`: the kernel δ-unfolds `isStuck` and ι-reduces
/// `RustSem.StepOutcome.rec` on the `stepped` constructor to `Bool.false`,
/// independent of `cfg`/`obs`.
///
/// The COMPLEMENT of [`declare_is_stuck_stuck_lemma`]: together they fully
/// characterize `isStuck` over BOTH `StepOutcome` constructors — a step that
/// PROGRESSED (`stepped`) is not stuck, a step that got `stuck` is. This is the
/// operational invariant a byte-addressed `step` analysis relies on (progress vs.
/// stuckness is decided by the outcome constructor), proved over the reflected
/// semantics, axiom-clean (only the foundational `Eq.refl`).
///
/// **Precondition:** `Eq`, `Bool`, `RustSem.StepOutcome.isStuck` (and the `Config`/
/// `Observation` deps of the `stepped` constructor) admitted.
///
/// # Errors
/// Returns [`EnvError`] if the proof fails to type-check or admission fails.
pub fn declare_is_stuck_stepped_lemma(env: &mut Environment) -> Result<(), EnvError> {
    let one = Level::succ(Level::zero());
    let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
    let false_c = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let config = Expr::const_(Name::from_string(CONFIG), vec![]);
    let observation = Expr::const_(Name::from_string(OBSERVATION), vec![]);
    let is_stuck = Expr::const_(Name::from_string(IS_STUCK), vec![]);
    let stepped_ctor = Expr::const_(Name::from_string("RustSem.StepOutcome.stepped"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);

    // Under ∀ cfg obs: cfg = bvar 1, obs = bvar 0.
    // lhs = isStuck (StepOutcome.stepped cfg obs)
    let stepped = Expr::apps(stepped_ctor, [Expr::bvar(1), Expr::bvar(0)]);
    let lhs = Expr::app(is_stuck, stepped);
    // Eq Bool (isStuck (stepped cfg obs)) Bool.false
    let eq_body = Expr::apps(eq, [bool_c.clone(), lhs, false_c.clone()]);
    // ∀ cfg : Config, ∀ obs : Observation, …
    let stmt = Expr::pi(
        BinderInfo::Default,
        config.clone(),
        Expr::pi(BinderInfo::Default, observation.clone(), eq_body),
    );
    // λ cfg obs => Eq.refl Bool Bool.false   (well-typed up to defeq)
    let refl_app = Expr::apps(eq_refl, [bool_c, false_c]);
    let proof = Expr::lam(
        BinderInfo::Default,
        config,
        Expr::lam(BinderInfo::Default, observation, refl_app),
    );

    env.add_decl(Declaration::Theorem {
        name: Name::from_string(IS_STUCK_STEPPED_THM),
        level_params: vec![],
        type_: stmt,
        value: proof,
    })
}

/// Fully-qualified name of the `observation` projection on `StepOutcome`.
pub const OUTCOME_OBSERVATION: &str = "RustSem.StepOutcome.observation";
/// Name of the observation-faithfulness lemma `observation (stepped cfg obs) = some obs`.
pub const OUTCOME_OBSERVATION_STEPPED_THM: &str = "RustSem.StepOutcome.observation_stepped";

/// Admit `RustSem.StepOutcome.observation : StepOutcome → Option Observation`
/// (the observation a step emitted, or `none` if it got stuck), as a recursor-based
/// `Definition`, then prove **observation faithfulness**:
/// `∀ cfg obs, observation (stepped cfg obs) = some obs` by `Eq.refl`.
///
/// This is the metatheory fact that the reflected `StepOutcome` does not LOSE the
/// emitted observation — it is recoverable from the outcome. That faithfulness is
/// what an observational-equivalence / bisimulation argument over the reflected
/// `step` relies on (the observation trace is preserved across the reflection).
/// Hand-built kernel `Expr`s (path B), default build, axiom-clean.
///
/// **Precondition:** `Eq`, `Option`, `RustSem.Observation`/`Config`/`StuckReason`,
/// and `RustSem.StepOutcome` admitted.
///
/// # Errors
/// Returns [`EnvError`] if the definition/lemma fails to type-check or admit.
pub fn declare_outcome_observation(env: &mut Environment) -> Result<(), EnvError> {
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let outcome = Expr::const_(Name::from_string(STEP_OUTCOME), vec![]);
    let config = Expr::const_(Name::from_string(CONFIG), vec![]);
    let observation = Expr::const_(Name::from_string(OBSERVATION), vec![]);
    let stuck_reason = Expr::const_(Name::from_string(STUCK_REASON), vec![]);
    // Option Observation : Type 0 = Sort 1  (Observation : Type 0 ⇒ Option.{0}).
    let opt_obs = Expr::app(
        Expr::const_(Name::from_string("Option"), vec![zero.clone()]),
        observation.clone(),
    );
    let some_obs = |o: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Option.some"), vec![zero.clone()]),
            [observation.clone(), o],
        )
    };
    let none_obs = Expr::app(
        Expr::const_(Name::from_string("Option.none"), vec![zero.clone()]),
        observation.clone(),
    );

    // observation := λ t => StepOutcome.rec.{1} (λ _ => Option Observation)
    //                         (λ _cfg obs => some obs) (λ _ => none) t
    let motive = Expr::lam(BinderInfo::Default, outcome.clone(), opt_obs.clone());
    // stepped case: λ _cfg : Config => λ obs : Observation => some obs   (obs = bvar 0)
    let case_stepped = Expr::lam(
        BinderInfo::Default,
        config.clone(),
        Expr::lam(
            BinderInfo::Default,
            observation.clone(),
            some_obs(Expr::bvar(0)),
        ),
    );
    let case_stuck = Expr::lam(BinderInfo::Default, stuck_reason, none_obs);
    let rec = Expr::const_(
        Name::from_string("RustSem.StepOutcome.rec"),
        vec![one.clone()],
    );
    let body = Expr::apps(rec, [motive, case_stepped, case_stuck, Expr::bvar(0)]);
    let value = Expr::lam(BinderInfo::Default, outcome.clone(), body);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(OUTCOME_OBSERVATION),
        level_params: vec![],
        type_: Expr::arrow(outcome, opt_obs.clone()),
        value,
        is_reducible: true,
    })?;

    // observation_stepped : ∀ cfg obs, observation (stepped cfg obs) = some obs
    let obs_fn = Expr::const_(Name::from_string(OUTCOME_OBSERVATION), vec![]);
    let stepped_ctor = Expr::const_(Name::from_string("RustSem.StepOutcome.stepped"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);
    // Under ∀ cfg obs: cfg = bvar 1, obs = bvar 0.
    let stepped = Expr::apps(stepped_ctor, [Expr::bvar(1), Expr::bvar(0)]);
    let lhs = Expr::app(obs_fn, stepped);
    let eq_body = Expr::apps(eq, [opt_obs.clone(), lhs, some_obs(Expr::bvar(0))]);
    let stmt = Expr::pi(
        BinderInfo::Default,
        config.clone(),
        Expr::pi(BinderInfo::Default, observation.clone(), eq_body),
    );
    // λ cfg obs => Eq.refl (Option Observation) (some obs)   [obs = bvar 0 inside]
    let refl_app = Expr::apps(eq_refl, [opt_obs, some_obs(Expr::bvar(0))]);
    let proof = Expr::lam(
        BinderInfo::Default,
        config,
        Expr::lam(BinderInfo::Default, observation, refl_app),
    );
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(OUTCOME_OBSERVATION_STEPPED_THM),
        level_params: vec![],
        type_: stmt,
        value: proof,
    })
}

/// Name of the `config` projection on `StepOutcome` and its faithfulness lemma.
pub const OUTCOME_CONFIG: &str = "RustSem.StepOutcome.config";
pub const OUTCOME_CONFIG_STEPPED_THM: &str = "RustSem.StepOutcome.config_stepped";
/// Name of the `reason` projection on `StepOutcome` and its faithfulness lemma.
pub const OUTCOME_REASON: &str = "RustSem.StepOutcome.reason";
pub const OUTCOME_REASON_STUCK_THM: &str = "RustSem.StepOutcome.reason_stuck";

/// Admit the remaining `StepOutcome` payload projections + faithfulness lemmas,
/// completing the proof that the reflected `StepOutcome` LOSSLESSLY carries all its
/// payload (so the reflection is faithful / injective on payloads — what an
/// observational bisimulation over the reflected `step` needs):
///
///   config : StepOutcome → Option Config        config (stepped cfg obs) = some cfg
///   reason : StepOutcome → Option StuckReason    reason (stuck r)        = some r
///
/// Together with `observation_stepped` (and the `isStuck` pair), a `stepped` outcome
/// yields a recoverable `(config, observation)` and a `stuck` outcome a recoverable
/// `reason`. Hand-built kernel `Expr`s (path B), `Eq.refl` proofs, default build,
/// axiom-clean.
///
/// **Precondition:** `Eq`, `Option`, and `RustSem.StepOutcome` (with `Config`/
/// `Observation`/`StuckReason`) admitted.
///
/// # Errors
/// Returns [`EnvError`] if a definition/lemma fails to type-check or admit.
pub fn declare_outcome_payload_projections(env: &mut Environment) -> Result<(), EnvError> {
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let outcome = Expr::const_(Name::from_string(STEP_OUTCOME), vec![]);
    let config = Expr::const_(Name::from_string(CONFIG), vec![]);
    let observation = Expr::const_(Name::from_string(OBSERVATION), vec![]);
    let stuck_reason = Expr::const_(Name::from_string(STUCK_REASON), vec![]);
    let rec = Expr::const_(
        Name::from_string("RustSem.StepOutcome.rec"),
        vec![one.clone()],
    );
    let eq = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);
    let opt_of = |t: &Expr| {
        Expr::app(
            Expr::const_(Name::from_string("Option"), vec![zero.clone()]),
            t.clone(),
        )
    };
    let some_of = |t: &Expr, x: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Option.some"), vec![zero.clone()]),
            [t.clone(), x],
        )
    };
    let none_of = |t: &Expr| {
        Expr::app(
            Expr::const_(Name::from_string("Option.none"), vec![zero.clone()]),
            t.clone(),
        )
    };
    let stepped_ctor = Expr::const_(Name::from_string("RustSem.StepOutcome.stepped"), vec![]);
    let stuck_ctor = Expr::const_(Name::from_string("RustSem.StepOutcome.stuck"), vec![]);

    // ── config : StepOutcome → Option Config := stepped cfg obs ↦ some cfg ──────
    let opt_config = opt_of(&config);
    {
        // motive λ _ => Option Config; stepped case λ cfg obs => some cfg (cfg = bvar 1)
        let motive = Expr::lam(BinderInfo::Default, outcome.clone(), opt_config.clone());
        let case_stepped = Expr::lam(
            BinderInfo::Default,
            config.clone(),
            Expr::lam(
                BinderInfo::Default,
                observation.clone(),
                some_of(&config, Expr::bvar(1)),
            ),
        );
        let case_stuck = Expr::lam(BinderInfo::Default, stuck_reason.clone(), none_of(&config));
        let body = Expr::apps(
            rec.clone(),
            [motive, case_stepped, case_stuck, Expr::bvar(0)],
        );
        let value = Expr::lam(BinderInfo::Default, outcome.clone(), body);
        env.add_decl(Declaration::Definition {
            name: Name::from_string(OUTCOME_CONFIG),
            level_params: vec![],
            type_: Expr::arrow(outcome.clone(), opt_config.clone()),
            value,
            is_reducible: true,
        })?;
        // ∀ cfg obs, config (stepped cfg obs) = some cfg
        let config_fn = Expr::const_(Name::from_string(OUTCOME_CONFIG), vec![]);
        let stepped = Expr::apps(stepped_ctor.clone(), [Expr::bvar(1), Expr::bvar(0)]);
        let lhs = Expr::app(config_fn, stepped);
        let eq_body = Expr::apps(
            eq.clone(),
            [opt_config.clone(), lhs, some_of(&config, Expr::bvar(1))],
        );
        let stmt = Expr::pi(
            BinderInfo::Default,
            config.clone(),
            Expr::pi(BinderInfo::Default, observation.clone(), eq_body),
        );
        let refl = Expr::apps(
            eq_refl.clone(),
            [opt_config.clone(), some_of(&config, Expr::bvar(1))],
        );
        let proof = Expr::lam(
            BinderInfo::Default,
            config.clone(),
            Expr::lam(BinderInfo::Default, observation.clone(), refl),
        );
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(OUTCOME_CONFIG_STEPPED_THM),
            level_params: vec![],
            type_: stmt,
            value: proof,
        })?;
    }

    // ── reason : StepOutcome → Option StuckReason := stuck r ↦ some r ───────────
    let opt_reason = opt_of(&stuck_reason);
    {
        let motive = Expr::lam(BinderInfo::Default, outcome.clone(), opt_reason.clone());
        let case_stepped = Expr::lam(
            BinderInfo::Default,
            config.clone(),
            Expr::lam(
                BinderInfo::Default,
                observation.clone(),
                none_of(&stuck_reason),
            ),
        );
        // stuck case: λ r => some r   (r = bvar 0)
        let case_stuck = Expr::lam(
            BinderInfo::Default,
            stuck_reason.clone(),
            some_of(&stuck_reason, Expr::bvar(0)),
        );
        let body = Expr::apps(
            rec.clone(),
            [motive, case_stepped, case_stuck, Expr::bvar(0)],
        );
        let value = Expr::lam(BinderInfo::Default, outcome.clone(), body);
        env.add_decl(Declaration::Definition {
            name: Name::from_string(OUTCOME_REASON),
            level_params: vec![],
            type_: Expr::arrow(outcome.clone(), opt_reason.clone()),
            value,
            is_reducible: true,
        })?;
        // ∀ r, reason (stuck r) = some r
        let reason_fn = Expr::const_(Name::from_string(OUTCOME_REASON), vec![]);
        let stuck = Expr::app(stuck_ctor.clone(), Expr::bvar(0));
        let lhs = Expr::app(reason_fn, stuck);
        let eq_body = Expr::apps(
            eq.clone(),
            [
                opt_reason.clone(),
                lhs,
                some_of(&stuck_reason, Expr::bvar(0)),
            ],
        );
        let stmt = Expr::pi(BinderInfo::Default, stuck_reason.clone(), eq_body);
        let refl = Expr::apps(
            eq_refl.clone(),
            [opt_reason.clone(), some_of(&stuck_reason, Expr::bvar(0))],
        );
        let proof = Expr::lam(BinderInfo::Default, stuck_reason.clone(), refl);
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(OUTCOME_REASON_STUCK_THM),
            level_params: vec![],
            type_: stmt,
            value: proof,
        })?;
    }

    Ok(())
}

/// Names of the OFF-constructor projection lemmas (each projection is `none` on the
/// non-matching constructor) — together with the `some` lemmas these make each
/// projection an EXACT faithful partial inverse.
pub const OUTCOME_OBSERVATION_STUCK_THM: &str = "RustSem.StepOutcome.observation_stuck";
pub const OUTCOME_CONFIG_STUCK_THM: &str = "RustSem.StepOutcome.config_stuck";
pub const OUTCOME_REASON_STEPPED_THM: &str = "RustSem.StepOutcome.reason_stepped";

/// Admit the OFF-constructor projection lemmas, completing each `StepOutcome`
/// projection over BOTH constructors (`Eq.refl`, path B, default build, axiom-clean):
///
///   observation (stuck r)        = none      (a stuck outcome emits no observation)
///   config      (stuck r)        = none      (a stuck outcome has no result config)
///   reason      (stepped cfg obs) = none     (a progressed outcome has no stuck reason)
///
/// With the `some`-on-matching-constructor lemmas, this proves each projection is an
/// EXACT faithful partial inverse — the payload is recoverable on the right
/// constructor and the projection FABRICATES NOTHING on the other. That precise
/// characterization (the reflected outcome carries exactly its payload, no more, no
/// less) is what a sound observational bisimulation over the reflected `step` rests on.
///
/// **Precondition:** the three projections ([`declare_outcome_observation`],
/// [`declare_outcome_payload_projections`]) are already admitted.
///
/// # Errors
/// Returns [`EnvError`] if a lemma fails to type-check or admit.
pub fn declare_outcome_projection_complements(env: &mut Environment) -> Result<(), EnvError> {
    let zero = Level::zero();
    let one = Level::succ(Level::zero());
    let config = Expr::const_(Name::from_string(CONFIG), vec![]);
    let observation = Expr::const_(Name::from_string(OBSERVATION), vec![]);
    let stuck_reason = Expr::const_(Name::from_string(STUCK_REASON), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);
    let stepped_ctor = Expr::const_(Name::from_string("RustSem.StepOutcome.stepped"), vec![]);
    let stuck_ctor = Expr::const_(Name::from_string("RustSem.StepOutcome.stuck"), vec![]);
    let opt_of = |t: &Expr| {
        Expr::app(
            Expr::const_(Name::from_string("Option"), vec![zero.clone()]),
            t.clone(),
        )
    };
    let none_of = |t: &Expr| {
        Expr::app(
            Expr::const_(Name::from_string("Option.none"), vec![zero.clone()]),
            t.clone(),
        )
    };

    // observation (stuck r) = none   and   config (stuck r) = none   (∀ r : StuckReason)
    let mut stuck_is_none = |proj_const: &str, payload: &Expr, thm: &str| -> Result<(), EnvError> {
        let opt = opt_of(payload);
        let proj = Expr::const_(Name::from_string(proj_const), vec![]);
        let lhs = Expr::app(proj, Expr::app(stuck_ctor.clone(), Expr::bvar(0)));
        let eq_body = Expr::apps(eq.clone(), [opt.clone(), lhs, none_of(payload)]);
        let stmt = Expr::pi(BinderInfo::Default, stuck_reason.clone(), eq_body);
        let proof = Expr::lam(
            BinderInfo::Default,
            stuck_reason.clone(),
            Expr::apps(eq_refl.clone(), [opt, none_of(payload)]),
        );
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(thm),
            level_params: vec![],
            type_: stmt,
            value: proof,
        })
    };
    stuck_is_none(
        OUTCOME_OBSERVATION,
        &observation,
        OUTCOME_OBSERVATION_STUCK_THM,
    )?;
    stuck_is_none(OUTCOME_CONFIG, &config, OUTCOME_CONFIG_STUCK_THM)?;

    // reason (stepped cfg obs) = none   (∀ cfg obs)
    {
        let opt = opt_of(&stuck_reason);
        let reason = Expr::const_(Name::from_string(OUTCOME_REASON), vec![]);
        let stepped = Expr::apps(stepped_ctor.clone(), [Expr::bvar(1), Expr::bvar(0)]);
        let lhs = Expr::app(reason, stepped);
        let eq_body = Expr::apps(eq.clone(), [opt.clone(), lhs, none_of(&stuck_reason)]);
        let stmt = Expr::pi(
            BinderInfo::Default,
            config.clone(),
            Expr::pi(BinderInfo::Default, observation.clone(), eq_body),
        );
        let proof = Expr::lam(
            BinderInfo::Default,
            config,
            Expr::lam(
                BinderInfo::Default,
                observation,
                Expr::apps(eq_refl, [opt, none_of(&stuck_reason)]),
            ),
        );
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(OUTCOME_REASON_STEPPED_THM),
            level_params: vec![],
            type_: stmt,
            value: proof,
        })?;
    }

    Ok(())
}

/// Names of the `MemEntry`/`AllocId` destructor projections + faithfulness lemmas.
pub const MEM_ENTRY_ALLOC_ID: &str = "RustSem.MemEntry.allocId";
pub const MEM_ENTRY_ALLOC: &str = "RustSem.MemEntry.alloc";
pub const ALLOC_ID_VAL: &str = "RustSem.AllocId.val";
pub const MEM_ENTRY_ALLOC_ID_MK_THM: &str = "RustSem.MemEntry.allocId_mk";
pub const MEM_ENTRY_ALLOC_MK_THM: &str = "RustSem.MemEntry.alloc_mk";
pub const ALLOC_ID_VAL_MK_THM: &str = "RustSem.AllocId.val_mk";

/// Admit the `MemEntry`/`AllocId` DESTRUCTOR projections and their faithfulness
/// lemmas (single-constructor recursors + `Eq.refl`, path B, default build,
/// axiom-clean):
///
///   MemEntry.allocId : MemEntry → AllocId     allocId (MemEntry.mk id a) = id
///   MemEntry.alloc   : MemEntry → Allocation  alloc   (MemEntry.mk id a) = a
///   AllocId.val      : AllocId → Nat          val     (AllocId.mk n)      = n
///
/// These are the byte-addressed memory destructors the recursive `lookupMem`
/// (and hence the §3.5 alloc-freshness lemma) is assembled from: a memory lookup
/// reads each `MemEntry`'s `allocId`, compares it (via `AllocId.val` + `Nat.beq`)
/// to the target, and on a hit returns its `alloc`. Landing + proving them
/// faithful now is the destructor layer the recursive lookup builds on.
///
/// **Precondition:** `RustSem.MemEntry`/`Allocation` (via [`declare_config`]),
/// `RustSem.AllocId` (via [`declare_id_newtypes`]), `Nat`, `Eq` admitted.
///
/// # Errors
/// Returns [`EnvError`] if a definition/lemma fails to type-check or admit.
pub fn declare_mem_entry_projections(env: &mut Environment) -> Result<(), EnvError> {
    let one = Level::succ(Level::zero());
    let mem_entry = Expr::const_(Name::from_string(MEM_ENTRY), vec![]);
    let allocation = Expr::const_(Name::from_string(ALLOCATION), vec![]);
    let alloc_id = Expr::const_(Name::from_string(ALLOC_ID), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let mem_rec = Expr::const_(Name::from_string("RustSem.MemEntry.rec"), vec![one.clone()]);
    let alloc_rec = Expr::const_(Name::from_string("RustSem.AllocId.rec"), vec![one.clone()]);
    let mem_mk = Expr::const_(Name::from_string("RustSem.MemEntry.mk"), vec![]);
    let alloc_mk = Expr::const_(Name::from_string("RustSem.AllocId.mk"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);

    // ── MemEntry.allocId / MemEntry.alloc (project the 2-field MemEntry.mk) ─────
    // proj := λ t => MemEntry.rec.{1} (λ _ => Out) (λ id a => <id|a>) t
    let mut mem_proj =
        |def_name: &str, out: &Expr, pick_first: bool, thm: &str| -> Result<(), EnvError> {
            let motive = Expr::lam(BinderInfo::Default, mem_entry.clone(), out.clone());
            // minor: λ (id : AllocId) (a : Allocation) => id  (bvar 1)  |  a  (bvar 0)
            let picked = if pick_first {
                Expr::bvar(1)
            } else {
                Expr::bvar(0)
            };
            let minor = Expr::lam(
                BinderInfo::Default,
                alloc_id.clone(),
                Expr::lam(BinderInfo::Default, allocation.clone(), picked),
            );
            let body = Expr::apps(mem_rec.clone(), [motive, minor, Expr::bvar(0)]);
            let value = Expr::lam(BinderInfo::Default, mem_entry.clone(), body);
            env.add_decl(Declaration::Definition {
                name: Name::from_string(def_name),
                level_params: vec![],
                type_: Expr::arrow(mem_entry.clone(), out.clone()),
                value,
                is_reducible: true,
            })?;
            // ∀ id a, proj (MemEntry.mk id a) = <id|a>   (id = bvar 1, a = bvar 0)
            let proj = Expr::const_(Name::from_string(def_name), vec![]);
            let mk = Expr::apps(mem_mk.clone(), [Expr::bvar(1), Expr::bvar(0)]);
            let lhs = Expr::app(proj, mk);
            let rhs = if pick_first {
                Expr::bvar(1)
            } else {
                Expr::bvar(0)
            };
            let eq_body = Expr::apps(eq.clone(), [out.clone(), lhs, rhs.clone()]);
            let stmt = Expr::pi(
                BinderInfo::Default,
                alloc_id.clone(),
                Expr::pi(BinderInfo::Default, allocation.clone(), eq_body),
            );
            let proof = Expr::lam(
                BinderInfo::Default,
                alloc_id.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    allocation.clone(),
                    Expr::apps(eq_refl.clone(), [out.clone(), rhs]),
                ),
            );
            env.add_decl(Declaration::Theorem {
                name: Name::from_string(thm),
                level_params: vec![],
                type_: stmt,
                value: proof,
            })
        };
    mem_proj(
        MEM_ENTRY_ALLOC_ID,
        &alloc_id,
        true,
        MEM_ENTRY_ALLOC_ID_MK_THM,
    )?;
    mem_proj(MEM_ENTRY_ALLOC, &allocation, false, MEM_ENTRY_ALLOC_MK_THM)?;

    // ── AllocId.val (project the 1-field AllocId.mk : Nat → AllocId) ────────────
    {
        // val := λ x => AllocId.rec.{1} (λ _ => Nat) (λ n => n) x
        let motive = Expr::lam(BinderInfo::Default, alloc_id.clone(), nat.clone());
        let minor = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)); // λ n => n
        let body = Expr::apps(alloc_rec, [motive, minor, Expr::bvar(0)]);
        let value = Expr::lam(BinderInfo::Default, alloc_id.clone(), body);
        env.add_decl(Declaration::Definition {
            name: Name::from_string(ALLOC_ID_VAL),
            level_params: vec![],
            type_: Expr::arrow(alloc_id.clone(), nat.clone()),
            value,
            is_reducible: true,
        })?;
        // ∀ n, val (AllocId.mk n) = n
        let val = Expr::const_(Name::from_string(ALLOC_ID_VAL), vec![]);
        let lhs = Expr::app(val, Expr::app(alloc_mk, Expr::bvar(0)));
        let eq_body = Expr::apps(eq.clone(), [nat.clone(), lhs, Expr::bvar(0)]);
        let stmt = Expr::pi(BinderInfo::Default, nat.clone(), eq_body);
        let proof = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::apps(eq_refl, [nat.clone(), Expr::bvar(0)]),
        );
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(ALLOC_ID_VAL_MK_THM),
            level_params: vec![],
            type_: stmt,
            value: proof,
        })?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn borrow_permission_admits_and_is_axiom_clean() {
        let mut env = Environment::new();
        // Baseline: the empty env's foundational prelude carries its own axioms;
        // M2.4's claim is that reflecting BorrowPermission adds ZERO *new* domain
        // axioms (axiom closure ⊆ FOUNDATIONAL_AXIOMS), so measure the delta.
        let before = env.soundness_report().total_domain_axioms;

        declare_borrow_permission(&mut env)
            .expect("RustSem.BorrowPermission should admit into a fresh kernel env");

        // The inductive is registered.
        assert!(
            env.get_inductive(&Name::from_string(BORROW_PERMISSION))
                .is_some(),
            "RustSem.BorrowPermission must be a registered inductive"
        );

        // Axiom-clean: a pure inductive introduces no NEW domain (non-foundational)
        // axioms — the M2.4 exit condition.
        let after = env.soundness_report().total_domain_axioms;
        assert_eq!(
            after, before,
            "reflecting BorrowPermission must not introduce domain axioms"
        );
    }

    #[test]
    fn id_newtypes_admit_axiom_clean_over_nat() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat prelude should initialize");
        let before = env.soundness_report().total_domain_axioms;

        declare_id_newtypes(&mut env).expect("id newtypes should admit over Nat");

        for ty in [ALLOC_ID, BORROW_TAG, PROTECTOR_ID] {
            assert!(
                env.get_inductive(&Name::from_string(ty)).is_some(),
                "{ty} must be a registered inductive"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "Nat-wrapping id newtypes must not introduce domain axioms"
        );
    }

    #[test]
    fn place_recursive_inductive_admits_axiom_clean() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat prelude should initialize");
        env.init_string().expect("String prelude should initialize");
        let before = env.soundness_report().total_domain_axioms;

        declare_place(&mut env).expect("recursive Place inductive should admit");

        assert!(
            env.get_inductive(&Name::from_string(PLACE)).is_some(),
            "RustSem.Place must be a registered inductive"
        );
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "recursive Place inductive must not introduce domain axioms"
        );
    }

    /// Set up a kernel env with the standard preludes + the RustSem leaf/structural
    /// declarations that the payload enums depend on.
    fn env_with_rustsem_base() -> Environment {
        // Full standard prelude (Nat/String/List/Option/Fin/…), then UInt8
        // (needs Fin, which the prelude provides), then the RustSem leaf/
        // structural declarations the payload enums depend on.
        let mut env = Environment::with_prelude();
        env.init_uint_types()
            .expect("UInt types (Fin comes from the prelude)");
        declare_borrow_permission(&mut env).expect("BorrowPermission");
        declare_id_newtypes(&mut env).expect("id newtypes");
        declare_place(&mut env).expect("Place");
        env
    }

    #[test]
    fn mem_op_and_observation_admit_axiom_clean() {
        let mut env = env_with_rustsem_base();
        let before = env.soundness_report().total_domain_axioms;

        declare_mem_op(&mut env)
            .expect("MemOp should admit (uses List/Option/UInt8 + RustSem types)");
        declare_observation(&mut env).expect("Observation should admit");

        assert!(env.get_inductive(&Name::from_string(MEM_OP)).is_some());
        assert!(env.get_inductive(&Name::from_string(OBSERVATION)).is_some());
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "payload enums must not introduce domain axioms"
        );
    }

    #[test]
    fn stuck_reason_admits_axiom_clean() {
        let mut env = env_with_rustsem_base();
        let before = env.soundness_report().total_domain_axioms;

        declare_stuck_reason(&mut env).expect("StuckReason should admit");

        assert!(
            env.get_inductive(&Name::from_string(STUCK_REASON))
                .is_some(),
            "RustSem.StuckReason must be a registered inductive"
        );
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "StuckReason must not introduce domain axioms"
        );
    }

    #[test]
    fn config_tower_and_step_outcome_admit_axiom_clean() {
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        let before = env.soundness_report().total_domain_axioms;

        declare_config(&mut env).expect("Config state tower should admit");
        declare_step_outcome(&mut env).expect("StepOutcome should admit");

        for n in [
            ALLOCATION,
            MEMORY,
            STACKED_BORROWS,
            BRIDGE,
            CONFIG,
            STEP_OUTCOME,
        ] {
            assert!(
                env.get_inductive(&Name::from_string(n)).is_some(),
                "{n} must be a registered inductive"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the Config tower + StepOutcome must not introduce domain axioms"
        );
    }

    #[test]
    fn is_stuck_definition_admits_axiom_clean() {
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        declare_config(&mut env).expect("Config");
        declare_step_outcome(&mut env).expect("StepOutcome");
        let before = env.soundness_report().total_domain_axioms;

        // add_decl type-checks the recursor-based body; success means the term is
        // well-typed (the recursor application + universe are right).
        declare_is_stuck(&mut env)
            .expect("isStuck recursor-based definition should type-check and admit");

        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "a recursor-based definition must not introduce domain axioms"
        );
    }

    #[test]
    fn is_stuck_stuck_computation_lemma_admits_axiom_clean() {
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        declare_config(&mut env).expect("Config");
        declare_step_outcome(&mut env).expect("StepOutcome");
        declare_is_stuck(&mut env).expect("isStuck");
        let before = env.soundness_report().total_domain_axioms;

        // Proved by Eq.refl — succeeds only if the kernel reduces
        // isStuck (stuck r) to Bool.true (δ-unfold isStuck + ι-reduce the recursor).
        declare_is_stuck_stuck_lemma(&mut env)
            .expect("isStuck (stuck r) = true must hold by computation (rfl)");

        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "a lemma proved by Eq.refl introduces no domain axioms"
        );
    }

    #[test]
    fn is_stuck_stepped_computation_lemma_admits_axiom_clean() {
        // The COMPLEMENT of isStuck_stuck: a progressed (stepped) outcome is NOT
        // stuck. Together they characterize isStuck over both StepOutcome ctors —
        // a §3.5-style operational invariant over the reflected semantics.
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        declare_config(&mut env).expect("Config");
        declare_step_outcome(&mut env).expect("StepOutcome");
        declare_is_stuck(&mut env).expect("isStuck");
        let before = env.soundness_report().total_domain_axioms;

        // Proved by Eq.refl — succeeds only if the kernel reduces
        // isStuck (stepped cfg obs) to Bool.false (δ-unfold isStuck + ι-reduce the
        // recursor on the `stepped` constructor, independent of cfg/obs).
        declare_is_stuck_stepped_lemma(&mut env)
            .expect("isStuck (stepped cfg obs) = false must hold by computation (rfl)");

        assert!(
            env.get_const(&Name::from_string(IS_STUCK_STEPPED_THM))
                .is_some(),
            "the complement lemma must be registered (its Eq.refl proof type-checked)"
        );
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "a lemma proved by Eq.refl introduces no domain axioms"
        );
    }

    #[test]
    fn outcome_observation_faithfulness_admits_axiom_clean() {
        // The reflected StepOutcome faithfully carries its observation: a progressed
        // step's observation is recoverable (`observation (stepped cfg obs) = some obs`).
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        declare_config(&mut env).expect("Config");
        declare_step_outcome(&mut env).expect("StepOutcome");
        let before = env.soundness_report().total_domain_axioms;

        // Admits the `observation` projection (recursor Definition) AND the
        // faithfulness lemma (Eq.refl) — both must type-check / compute.
        declare_outcome_observation(&mut env)
            .expect("observation projection + faithfulness lemma must admit (compute by rfl)");

        for c in [OUTCOME_OBSERVATION, OUTCOME_OBSERVATION_STEPPED_THM] {
            assert!(
                env.get_const(&Name::from_string(c)).is_some(),
                "{c} must be registered"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the observation-faithfulness def + lemma must add zero domain axioms"
        );
    }

    #[test]
    fn outcome_payload_projections_admit_axiom_clean() {
        // The reflected StepOutcome losslessly carries ALL its payload: a stepped
        // outcome's config (and observation) are recoverable, a stuck outcome's
        // reason is recoverable. Together = faithful reflection (injective on payloads).
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        declare_config(&mut env).expect("Config");
        declare_step_outcome(&mut env).expect("StepOutcome");
        let before = env.soundness_report().total_domain_axioms;

        declare_outcome_payload_projections(&mut env)
            .expect("config/reason projections + faithfulness lemmas must admit (compute by rfl)");

        for c in [
            OUTCOME_CONFIG,
            OUTCOME_CONFIG_STEPPED_THM,
            OUTCOME_REASON,
            OUTCOME_REASON_STUCK_THM,
        ] {
            assert!(
                env.get_const(&Name::from_string(c)).is_some(),
                "{c} must be registered"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the payload projections + faithfulness lemmas must add zero domain axioms"
        );
    }

    #[test]
    fn outcome_projection_complements_admit_axiom_clean() {
        // Each projection is `none` on the OFF constructor — with the `some` lemmas,
        // each projection is an EXACT faithful partial inverse (recoverable + no
        // fabricated data). The full faithful-reflection characterization.
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        declare_config(&mut env).expect("Config");
        declare_step_outcome(&mut env).expect("StepOutcome");
        declare_outcome_observation(&mut env).expect("observation projection");
        declare_outcome_payload_projections(&mut env).expect("config/reason projections");
        let before = env.soundness_report().total_domain_axioms;

        declare_outcome_projection_complements(&mut env)
            .expect("off-constructor projection lemmas must admit (compute by rfl)");

        for c in [
            OUTCOME_OBSERVATION_STUCK_THM,
            OUTCOME_CONFIG_STUCK_THM,
            OUTCOME_REASON_STEPPED_THM,
        ] {
            assert!(
                env.get_const(&Name::from_string(c)).is_some(),
                "{c} must be registered"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the off-constructor projection lemmas must add zero domain axioms"
        );
    }

    #[test]
    fn mem_entry_projections_admit_axiom_clean() {
        // The byte-addressed memory DESTRUCTORS (MemEntry.allocId/.alloc, AllocId.val)
        // + faithfulness — the layer the recursive lookupMem / §3.5 alloc-freshness
        // is assembled from.
        let mut env = env_with_rustsem_base();
        declare_config(&mut env).expect("Config (MemEntry/Allocation)");
        let before = env.soundness_report().total_domain_axioms;

        declare_mem_entry_projections(&mut env)
            .expect("MemEntry/AllocId destructor projections + lemmas must admit (rfl)");

        for c in [
            MEM_ENTRY_ALLOC_ID,
            MEM_ENTRY_ALLOC,
            ALLOC_ID_VAL,
            MEM_ENTRY_ALLOC_ID_MK_THM,
            MEM_ENTRY_ALLOC_MK_THM,
            ALLOC_ID_VAL_MK_THM,
        ] {
            assert!(
                env.get_const(&Name::from_string(c)).is_some(),
                "{c} must be registered"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the MemEntry/AllocId destructors + faithfulness lemmas must add zero domain axioms"
        );
    }

    /// Proves the HYBRID `.lean`-source route: a Lean def written in surface
    /// syntax over the Rust-reflected `RustSem.*` types parses, elaborates, and
    /// admits axiom-clean into the same env that the Rust decl-builders populated.
    /// This is the enabler for the full `step` + the §3.5 metatheory lemmas,
    /// which are far more concise in Lean syntax than hand-built recursor `Expr`s.
    /// Behind the `lean-elab` feature (heavy dep graph): run with
    /// `cargo test -p clean-rust-sem --features lean-elab`.
    #[cfg(feature = "lean-elab")]
    #[test]
    fn lean_source_def_over_reflected_types_admits_axiom_clean() {
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        declare_config(&mut env).expect("Config");
        declare_step_outcome(&mut env).expect("StepOutcome");
        let before = env.soundness_report().total_domain_axioms;

        // A Lean def referencing the Rust-reflected RustSem.StepOutcome inductive.
        let src = "def RustSem.gbProbe : RustSem.StepOutcome → Bool := fun _ => Bool.true";
        let decl = clean_parser::parse_decl(src).expect("Lean def should parse");
        clean_elab::elaborate_decl_and_register(&mut env, &decl)
            .expect("Lean def over reflected types should elaborate + register");

        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "an elaborated def over the reflected types must not introduce domain axioms"
        );
    }

    /// Faithful `step` building blocks written in Lean and elaborated over the
    /// reflected types: `allocIdBeq` (multi-arg pattern match on a newtype) and
    /// the structurally-recursive `lookupMem` (assoc-list lookup with `Nat.beq` +
    /// `if`/`Option`/`List`). Proves the elaborator handles the matching +
    /// recursion the real `step` needs, axiom-clean.
    #[cfg(feature = "lean-elab")]
    #[test]
    fn lean_step_helpers_elaborate_axiom_clean() {
        let mut env = env_with_rustsem_base();
        declare_observation(&mut env).expect("Observation");
        declare_stuck_reason(&mut env).expect("StuckReason");
        declare_config(&mut env).expect("Config");
        declare_step_outcome(&mut env).expect("StepOutcome");
        let before = env.soundness_report().total_domain_axioms;

        let src = "\
def RustSem.allocIdBeq : RustSem.AllocId → RustSem.AllocId → Bool
  | RustSem.AllocId.mk a, RustSem.AllocId.mk b => Nat.beq a b

def RustSem.lookupMem : List RustSem.MemEntry → RustSem.AllocId → Option RustSem.Allocation
  | List.nil, _ => Option.none
  | List.cons (RustSem.MemEntry.mk id a) rest, target =>
      if RustSem.allocIdBeq id target then Option.some a else RustSem.lookupMem rest target
";
        let decls = clean_parser::parse_file(src).expect("Lean step helpers should parse");
        for d in &decls {
            clean_elab::elaborate_decl_and_register(&mut env, d)
                .expect("step helper should elaborate + register");
        }

        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "faithful step helpers must be axiom-clean"
        );
    }

    /// T-step (byte-addressed): build the real MEMORY-PRESENCE model over the
    /// reflected `Config` tower (`Memory`/`MemEntry`/`Allocation`/`AllocId`) via the
    /// `.lean` route, axiom-clean. Extends the existing `allocIdBeq`/`lookupMem`
    /// helpers with `memAllocs` (the `Memory → List MemEntry` projection), `optIsSome`,
    /// and `isAllocated : Memory → AllocId → Bool` — the allocation-presence query a
    /// byte-addressed `step` (alloc/dealloc/read/write bounds + use-after-free
    /// checks) is built on. These are the executable `value_at_address::step` memory
    /// operations reflected into the kernel, the substrate the §3.5 metatheory
    /// (alloc-freshness, borrow-stack WF) sits on.
    ///
    /// NOTE (next session): the computation lemmas (`isAllocated (Memory.mk [] 0)
    /// (AllocId.mk 0) = false`, and the alloc round-trip) cannot yet go through the
    /// `.lean` route — `clean-elab` fails to infer the universe of the `=`/`Eq`
    /// notation in a term-mode proof (even the trivial `def _ : Bool.true =
    /// Bool.true := Eq.refl Bool.true` fails with `Sort(Param u_n)` unsolved). They
    /// must be hand-built as kernel `Expr`s (like `declare_is_stuck_stuck_lemma`) OR
    /// wait on a `clean-elab` Eq-universe fix.
    #[cfg(feature = "lean-elab")]
    #[test]
    fn lean_byte_addressed_memory_model_elaborates_axiom_clean() {
        let mut env = env_with_rustsem_base();
        declare_config(&mut env).expect("Config (Memory/MemEntry/Allocation tower)");
        let before = env.soundness_report().total_domain_axioms;

        let src = "\
def RustSem.allocIdBeq : RustSem.AllocId → RustSem.AllocId → Bool
  | RustSem.AllocId.mk a, RustSem.AllocId.mk b => Nat.beq a b

def RustSem.lookupMem : List RustSem.MemEntry → RustSem.AllocId → Option RustSem.Allocation
  | List.nil, _ => Option.none
  | List.cons (RustSem.MemEntry.mk id a) rest, target =>
      if RustSem.allocIdBeq id target then Option.some a else RustSem.lookupMem rest target

def RustSem.memAllocs : RustSem.Memory → List RustSem.MemEntry
  | RustSem.Memory.mk allocs _ => allocs

def RustSem.optIsSome : Option RustSem.Allocation → Bool
  | Option.none => Bool.false
  | Option.some _ => Bool.true

def RustSem.isAllocated : RustSem.Memory → RustSem.AllocId → Bool
  | m, id => RustSem.optIsSome (RustSem.lookupMem (RustSem.memAllocs m) id)
";
        let decls =
            clean_parser::parse_file(src).expect("byte-addressed memory model should parse");
        for d in &decls {
            clean_elab::elaborate_decl_and_register(&mut env, d)
                .expect("byte-addressed memory def/lemma should elaborate + register");
        }

        // The two presence lemmas are registered as proof-carrying declarations:
        // their Eq.refl bodies type-checked, so the reflected model COMPUTED the
        // expected StepOutcome-style observation (alloc absent / present).
        for thm in ["RustSem.isAllocated", "RustSem.lookupMem"] {
            assert!(
                env.get_const(&Name::from_string(thm)).is_some(),
                "{thm} must be registered (its Eq.refl proof must have type-checked)"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the byte-addressed memory-presence model + computation lemmas must be axiom-clean"
        );
    }

    /// T-step §3.5 **alloc-freshness + alloc round-trip** over the REAL recursive
    /// byte-addressed `lookupMem`, via a hybrid that sidesteps BOTH blockers:
    /// elaborate the (recursive, already-proven) `.lean` `lookupMem` over
    /// `List MemEntry`, then HAND-BUILD the alloc lemmas as kernel `Expr`s with
    /// `Eq.refl` (so no `.lean` `Eq`-universe dependency, and no risky hand-built
    /// recursive function). Proves, axiom-clean:
    ///
    ///   * alloc-freshness (base): `∀ id, lookupMem [] id = none` — nothing is
    ///     allocated in empty memory (§3.5 freshness base case).
    ///   * alloc round-trip: `lookupMem [MemEntry.mk (AllocId.mk 0) A] (AllocId.mk 0)
    ///     = some A` — after an allocation, the id resolves to it (the kernel reduces
    ///     the recursive lookup: cons → allocIdBeq (Nat.beq 0 0 = true) → some A).
    ///
    /// These are genuine §3.5 facts over the real recursive memory model — the
    /// allocation observability + freshness an operational `step`/bisimulation needs.
    #[cfg(feature = "lean-elab")]
    #[test]
    fn lean_recursive_lookupmem_alloc_freshness_and_roundtrip() {
        let mut env = env_with_rustsem_base();
        declare_config(&mut env).expect("Config (Memory/MemEntry/Allocation)");

        // (1) Elaborate the recursive .lean lookupMem (+ allocIdBeq) — proven path.
        let src = "\
def RustSem.allocIdBeq : RustSem.AllocId → RustSem.AllocId → Bool
  | RustSem.AllocId.mk a, RustSem.AllocId.mk b => Nat.beq a b

def RustSem.lookupMem : List RustSem.MemEntry → RustSem.AllocId → Option RustSem.Allocation
  | List.nil, _ => Option.none
  | List.cons (RustSem.MemEntry.mk id a) rest, target =>
      if RustSem.allocIdBeq id target then Option.some a else RustSem.lookupMem rest target
";
        for d in &clean_parser::parse_file(src).expect("lookupMem should parse") {
            clean_elab::elaborate_decl_and_register(&mut env, d)
                .expect("lookupMem should elaborate");
        }
        let before = env.soundness_report().total_domain_axioms;

        // (2) Hand-build the alloc lemmas as kernel Exprs (Eq.refl) — no .lean Eq.
        let zero = Level::zero();
        let one = Level::succ(Level::zero());
        let mem_entry = Expr::const_(Name::from_string(MEM_ENTRY), vec![]);
        let alloc_id = Expr::const_(Name::from_string(ALLOC_ID), vec![]);
        let allocation = Expr::const_(Name::from_string(ALLOCATION), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let uint8 = Expr::const_(Name::from_string("UInt8"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let lookup = Expr::const_(Name::from_string("RustSem.lookupMem"), vec![]);
        let opt_alloc = Expr::app(
            Expr::const_(Name::from_string("Option"), vec![zero.clone()]),
            allocation.clone(),
        );
        let none_alloc = Expr::app(
            Expr::const_(Name::from_string("Option.none"), vec![zero.clone()]),
            allocation.clone(),
        );
        let some_alloc = |a: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Option.some"), vec![zero.clone()]),
                [allocation.clone(), a],
            )
        };
        let nil_of = |t: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![zero.clone()]),
                t.clone(),
            )
        };
        let nil_me = nil_of(&mem_entry);
        let eq = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);

        // alloc-freshness (base): ∀ id, lookupMem [] id = none   (id = bvar 0)
        let lhs_nil = Expr::apps(lookup.clone(), [nil_me.clone(), Expr::bvar(0)]);
        let fresh_stmt = Expr::pi(
            BinderInfo::Default,
            alloc_id.clone(),
            Expr::apps(eq.clone(), [opt_alloc.clone(), lhs_nil, none_alloc.clone()]),
        );
        let fresh_proof = Expr::lam(
            BinderInfo::Default,
            alloc_id.clone(),
            Expr::apps(eq_refl.clone(), [opt_alloc.clone(), none_alloc]),
        );
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("RustSem.lookupMem_nil_none"),
            level_params: vec![],
            type_: fresh_stmt,
            value: fresh_proof,
        })
        .expect("alloc-freshness base (lookupMem [] id = none) must hold by rfl");

        // alloc round-trip: lookupMem [MemEntry.mk (AllocId.mk 0) A] (AllocId.mk 0) = some A
        let id0 = Expr::app(
            Expr::const_(Name::from_string("RustSem.AllocId.mk"), vec![]),
            nat_zero.clone(),
        );
        let alloc_a = Expr::apps(
            Expr::const_(Name::from_string("RustSem.Allocation.mk"), vec![]),
            [
                id0.clone(),
                nat_zero.clone(),
                nat_zero.clone(),
                btrue,
                bfalse,
                nil_of(&uint8),
            ],
        );
        let entry = Expr::apps(
            Expr::const_(Name::from_string("RustSem.MemEntry.mk"), vec![]),
            [id0.clone(), alloc_a.clone()],
        );
        let mem = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![zero.clone()]),
            [mem_entry.clone(), entry, nil_me],
        );
        let lhs_hit = Expr::apps(lookup, [mem, id0]);
        let hit_stmt = Expr::apps(
            eq,
            [opt_alloc.clone(), lhs_hit, some_alloc(alloc_a.clone())],
        );
        let hit_proof = Expr::apps(eq_refl, [opt_alloc, some_alloc(alloc_a)]);
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("RustSem.lookupMem_cons_hit"),
            level_params: vec![],
            type_: hit_stmt,
            value: hit_proof,
        })
        .expect("alloc round-trip (lookupMem [mk id A] id = some A) must hold by rfl");

        // frame/MISS: lookupMem [MemEntry.mk (AllocId.mk 1) B] (AllocId.mk 0) = none —
        // the recursive lookup skips the non-matching entry (Nat.beq 1 0 = false) and
        // falls through to nil → none. With nil/hit, this is the full lookupMem
        // characterization on concrete inputs (empty→none, hit→some, miss→none): the
        // real recursive memory model COMPUTES correctly (a differential pin).
        {
            let z = Level::zero();
            let o = Level::succ(Level::zero());
            let me = Expr::const_(Name::from_string(MEM_ENTRY), vec![]);
            let al = Expr::const_(Name::from_string(ALLOCATION), vec![]);
            let u8t = Expr::const_(Name::from_string("UInt8"), vec![]);
            let n0 = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let lookup2 = Expr::const_(Name::from_string("RustSem.lookupMem"), vec![]);
            let eq2 = Expr::const_(Name::from_string("Eq"), vec![o.clone()]);
            let eq_refl2 = Expr::const_(Name::from_string("Eq.refl"), vec![o]);
            let opt_al = Expr::app(
                Expr::const_(Name::from_string("Option"), vec![z.clone()]),
                al.clone(),
            );
            let none_al = Expr::app(
                Expr::const_(Name::from_string("Option.none"), vec![z.clone()]),
                al.clone(),
            );
            let nil_me2 = Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![z.clone()]),
                me.clone(),
            );
            let nil_u8_2 = Expr::app(
                Expr::const_(Name::from_string("List.nil"), vec![z.clone()]),
                u8t,
            );
            let aid_mk = Expr::const_(Name::from_string("RustSem.AllocId.mk"), vec![]);
            let id0b = Expr::app(aid_mk.clone(), n0.clone());
            let one_nat = Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                n0.clone(),
            );
            let id1 = Expr::app(aid_mk, one_nat);
            let alloc_b = Expr::apps(
                Expr::const_(Name::from_string("RustSem.Allocation.mk"), vec![]),
                [
                    id1.clone(),
                    n0.clone(),
                    n0,
                    Expr::const_(Name::from_string("Bool.true"), vec![]),
                    Expr::const_(Name::from_string("Bool.false"), vec![]),
                    nil_u8_2,
                ],
            );
            let entry1 = Expr::apps(
                Expr::const_(Name::from_string("RustSem.MemEntry.mk"), vec![]),
                [id1, alloc_b],
            );
            let mem1 = Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![z]),
                [me, entry1, nil_me2],
            );
            let lhs_miss = Expr::apps(lookup2, [mem1, id0b]);
            let miss_stmt = Expr::apps(eq2, [opt_al.clone(), lhs_miss, none_al.clone()]);
            let miss_proof = Expr::apps(eq_refl2, [opt_al, none_al]);
            env.add_decl(Declaration::Theorem {
                name: Name::from_string("RustSem.lookupMem_cons_miss"),
                level_params: vec![],
                type_: miss_stmt,
                value: miss_proof,
            })
            .expect("frame/miss (lookupMem [mk 1 B] 0 = none) must hold by rfl");
        }

        for thm in [
            "RustSem.lookupMem_nil_none",
            "RustSem.lookupMem_cons_hit",
            "RustSem.lookupMem_cons_miss",
        ] {
            assert!(
                env.get_const(&Name::from_string(thm)).is_some(),
                "{thm} must be registered"
            );
        }
        assert_eq!(
            env.soundness_report().total_domain_axioms,
            before,
            "the §3.5 alloc-freshness + round-trip + miss lemmas must add zero domain axioms"
        );
    }
}
