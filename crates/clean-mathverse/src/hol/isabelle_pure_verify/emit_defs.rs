// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shard emission of the **translator-synthesized definitional constants**
//! (`isabelle.def.*`, `isabelle.polyinst.*`, `isabelle.inst.*`,
//! `isabelle.instk.*`, `isabelle.listfn.*`, `isabelle.method.*`).
//!
//! # Why this exists
//!
//! The Isabelle embedding mints a δ-unfolding `Definition` for every HOL
//! connective, class predicate, class method, instance operation and list
//! function it routes, so that (a) the constant's own `_def` axiom verifies
//! *reflexively* and (b) every use-site shares one head symbol. Those
//! definitions were registered into the replay [`Environment`] by the five
//! registration sweeps in [`super::register`] and the bootstrap in
//! [`super::streaming::register_builtin_def_consts`] — and then **died with the
//! process**. Neither path was ever handed the [`ShardWriter`].
//!
//! The theorems that DID reach the shard reference those constants in their
//! types and proof values, so the consumer's dependency loader resolves the
//! reference against a shard that never declared it and fails closed with
//!
//! ```text
//! dependency loader rejected `HOL.eqTrueI`: checked registration for dependency
//! `isabelle.s74896` failed: Type check error in declaration isabelle.s74896:
//! Unknown constant: isabelle.def.HOL.True
//! ```
//!
//! This is the same class of writer-side omission as the level-list bug: the
//! reader requires something the writer dropped.
//!
//! # Soundness
//!
//! Every value emitted by `emit_synthesized_def_consts` must carry the
//! kernel's `FullKernelCheck` provenance
//! and pass a fresh `check_decl_readonly_strict` over its exact stored
//! declaration before any writer mutation. Namespace, kind and value presence
//! select candidates; they do not establish verification. Missing provenance,
//! structural-only residents and a value that no longer checks are not emitted.
//! The [`ImportConfidence::KernelVerified`] stamp therefore rests on a local
//! safe, total kernel check as well as the original admission record.
//!
//! Two consequences are load-bearing and deliberate:
//!
//! * We emit the **kernel's stored** `type_` / `value` / `level_params`, not
//!   the pre-`add_decl` declaration. What is stamped is byte-identical to what
//!   was checked.
//! * A candidate that lacks full admission provenance or fails the fresh
//!   check is not emitted, even if a structural import left it resident.
//!   The registration sweeps' original `accepted`/`is_ok()` guards remain;
//!   this emission boundary also enforces its own check.
//!
//! Value-less declarations can never be emitted by
//! [`emit_synthesized_def_consts`]: `Num` and its constructors/recursor
//! (installed by `register_datatype_inductives` through the kernel's checked
//! `add_inductive`) carry no value, are not in the `isabelle.*` namespace, and
//! are filtered out twice over. They are emitted instead by
//! [`emit_inductive_families`], at the honest **non**-`KernelVerified`
//! confidence — see that function's soundness note.

use clean_kernel::env::{ConstantInfo, ConstantKind, DeclarationVerification};
use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment};

use super::super::isabelle_pure_translate::DATATYPE_INDUCTIVE_ROOTS;
use super::super::opentheory_shard::lower_kernel_expr;
use super::{PureVerifiedImport, WrittenConstant};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// Namespace of every constant the Isabelle lane mints into the replay
/// environment.
const ISA_PREFIX: &str = "isabelle.";

/// Trusted-ledger restatement axioms. Value-less by construction (so the
/// value guard below already excludes them); named here so the intent is
/// explicit rather than incidental — a ledger axiom must NEVER be stamped
/// `KernelVerified`.
const LEDGER_PREFIX: &str = "isabelle.trusted.";

/// Anonymous-node kernel identity (`isabelle.anon.<index>`). A *theorem*, not a
/// synthesized definition; written by the per-line shard write in
/// [`super::batch`].
const ANON_PREFIX: &str = "isabelle.anon.";

/// Is `name` a per-theorem serial identity (`isabelle.s<digits>`)?
///
/// Those are theorems written by the per-line path, not synthesized
/// definitions. The digit check (rather than a bare `isabelle.s` prefix test)
/// keeps a future `isabelle.set…`-style family from being silently skipped.
fn is_serial_identity(name: &str) -> bool {
    match name.strip_prefix("isabelle.s") {
        Some(rest) => !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()),
        None => false,
    }
}

/// Should `info` be emitted as a synthesized definitional constant?
///
/// Fail-closed on every axis: `isabelle.*`-namespaced, value-bearing, and a
/// `Definition`/`Opaque` kind. Anything else — prelude constants, inductives
/// and their constructors/recursors, ledger axioms, per-theorem records —
/// is skipped.
fn is_synthesized_def(info: &ConstantInfo) -> bool {
    let name = info.name.to_string();
    name.starts_with(ISA_PREFIX)
        && !name.starts_with(LEDGER_PREFIX)
        && !name.starts_with(ANON_PREFIX)
        && !is_serial_identity(&name)
        && info.value.is_some()
        && matches!(info.kind, ConstantKind::Definition | ConstantKind::Opaque)
}

/// Emit every kernel-accepted synthesized definitional constant resident in
/// `env` to `writer` as [`ImportConfidence::KernelVerified`], and return how
/// many were written.
///
/// Call this **once**, after the bootstrap + the five registration sweeps have
/// populated `env` and before the per-theorem verify loop. At that point the
/// `isabelle.*` residents are exactly the synthesized definitions.
///
/// Emission order is **name-ascending**, not [`Environment::constants`] hash
/// order, so two runs over the same corpus produce byte-identical shards.
/// Ordering has no bearing on the consumer: it topologically sorts the closure
/// itself (`mathverse_env.rs::topological_order`).
pub(super) fn emit_synthesized_def_consts(
    env: &Environment,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
) -> usize {
    let mut pending: Vec<&ConstantInfo> =
        env.constants().filter(|i| is_synthesized_def(i)).collect();
    pending.sort_by_key(|i| i.name.to_string());

    let mut written = 0usize;
    for info in pending {
        let Some(value) = info.value.as_ref() else {
            // Unreachable: `is_synthesized_def` required a value. Skipping
            // rather than unwrapping keeps the writer total.
            continue;
        };
        if env.declaration_verification(&info.name)
            != Some(DeclarationVerification::FullKernelCheck)
        {
            continue;
        }
        let declaration = match info.kind {
            ConstantKind::Definition => Declaration::Definition {
                name: info.name.clone(),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
                value: value.clone(),
                is_reducible: info.is_reducible,
            },
            ConstantKind::Opaque => Declaration::Opaque {
                name: info.name.clone(),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
                value: value.clone(),
            },
            _ => continue,
        };
        if env.check_decl_readonly_strict(&declaration).is_err() {
            continue;
        }
        let name = info.name.to_string();
        let name_idx = writer.add_string(&name);
        let type_idx = lower_kernel_expr(&info.type_, writer);
        let value_idx = lower_kernel_expr(value, writer);
        // Universe parameters must round-trip: `isabelle.def.HOL.If` is
        // universe-polymorphic (`level_params: ["u"]`), and dropping its
        // parameter list makes every consumer's `Const(isabelle.def.HOL.If,
        // [u])` fail checked registration with `LevelCountMismatch` — the exact
        // failure the shard-writer level-list fix removed elsewhere.
        let level_names: Vec<String> = info.level_params.iter().map(ToString::to_string).collect();
        let level_refs: Vec<&str> = level_names.iter().map(String::as_str).collect();
        let level_params_start = writer.add_string_block(&level_refs);
        let decl_kind = match info.kind {
            ConstantKind::Opaque => DeclKind::Opaque,
            _ => DeclKind::Definition,
        };
        let shard_idx = writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Isabelle as u8,
            // The exact stored declaration passed a fresh strict kernel check
            // above, in addition to its FullKernelCheck admission provenance.
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::Logic as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: AxiomProfile(0),
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start,
            level_params_count: u16::try_from(level_refs.len()).unwrap_or(0),
            _pad2: [0u8; 26],
        });
        out.written_constants.push(WrittenConstant {
            name,
            shard_idx,
            confidence: ImportConfidence::KernelVerified as u8,
            ledger_note: Some(
                "synthesized definitional constant; value type-checked by Environment::add_decl \
                 during closure replay"
                    .to_string(),
            ),
        });
        written += 1;
    }
    written
}

/// One staged shard row of an inductive family, resolved out of the kernel's
/// own side tables.
///
/// Staged (rather than written as it is discovered) so a family that cannot be
/// fully resolved writes **no** rows at all. A half-written family is worse
/// than none: the consumer's `build_inductive_replay_metadata` returns
/// `Ok(None)` for the WHOLE family when a single constructor row disagrees on
/// arity or level params, so a partial emission would convert a clean
/// "undeclared" failure into a silent replay decline.
struct FamilyRow<'a> {
    name: String,
    decl_kind: DeclKind,
    type_: &'a clean_kernel::Expr,
    /// `Some` only for the value-bearing auxiliary eliminators
    /// (`casesOn` / `recOn`); the skeleton members are value-less.
    value: Option<&'a clean_kernel::Expr>,
    level_params: Vec<String>,
    /// `Some((num_params, all_names))` on the inductive type former only.
    inductive_meta: Option<(u32, Vec<String>)>,
    confidence: ImportConfidence,
    ledger_note: &'static str,
}

/// The honest provenance note for a value-less family member.
const SKELETON_NOTE: &str = "inductive-family skeleton member (value-less); NOT kernel-verified \
     here — the consumer re-derives the family through the kernel's checked \
     Environment::add_inductive at replay time";

/// Resolve the inductive family rooted at `root_name` into the exact row set
/// the consumer's checked replay reads, or `None` if any member is missing
/// from the kernel's side tables (fail closed: emit nothing).
fn stage_family<'a>(env: &'a Environment, root_name: &str) -> Option<Vec<FamilyRow<'a>>> {
    let root = env.get_inductive(&Name::from_string(root_name))?;
    let members: Vec<Name> = if root.all_names.is_empty() {
        vec![root.name.clone()]
    } else {
        root.all_names.clone()
    };
    let all_names: Vec<String> = members.iter().map(ToString::to_string).collect();
    // The consumer requires every member's and every constructor's level-param
    // list to equal the ROOT's exactly. Enforce it writer-side so a family that
    // could never replay is never written.
    let root_levels: Vec<String> = root.level_params.iter().map(ToString::to_string).collect();

    let mut rows: Vec<FamilyRow<'a>> = Vec::new();
    for member in &members {
        let ind = env.get_inductive(member)?;
        let member_levels: Vec<String> = ind.level_params.iter().map(ToString::to_string).collect();
        if member_levels != root_levels {
            return None;
        }
        rows.push(FamilyRow {
            name: member.to_string(),
            decl_kind: DeclKind::Inductive,
            type_: &ind.type_,
            value: None,
            level_params: member_levels,
            inductive_meta: Some((ind.num_params, all_names.clone())),
            confidence: ImportConfidence::Axiomatized,
            ledger_note: SKELETON_NOTE,
        });
        // Constructors in the kernel's stored DECLARATION order.
        for ctor_name in &ind.constructor_names {
            let ctor = env.get_constructor(ctor_name)?;
            let ctor_levels: Vec<String> =
                ctor.level_params.iter().map(ToString::to_string).collect();
            if ctor_levels != root_levels {
                return None;
            }
            rows.push(FamilyRow {
                name: ctor_name.to_string(),
                decl_kind: DeclKind::Constructor,
                type_: &ctor.type_,
                value: None,
                level_params: ctor_levels,
                inductive_meta: None,
                confidence: ImportConfidence::Axiomatized,
                ledger_note: SKELETON_NOTE,
            });
        }
        // `{member}.rec` is NOT optional: the consumer derives the constructor
        // declaration order from the SHARD's stored rec type
        // (`ctor_order_from_shard_rec`). Without it the order falls back to
        // shard scan order — name-ascending here — and `Num` would replay as
        // `Bit0, Bit1, One`, regenerating a `Num.rec` with permuted minors that
        // no citing proof term can apply. Silently wrong is the worst outcome.
        let rec_name = Name::from_string(&format!("{member}.rec"));
        let rec = env.get_recursor(&rec_name)?;
        rows.push(FamilyRow {
            name: rec_name.to_string(),
            decl_kind: DeclKind::Recursor,
            type_: &rec.type_,
            value: None,
            // The recursor carries its own motive universe parameter, so its
            // level list legitimately differs from the family's.
            level_params: rec.level_params.iter().map(ToString::to_string).collect(),
            inductive_meta: None,
            confidence: ImportConfidence::Axiomatized,
            ledger_note: SKELETON_NOTE,
        });
        // The AUXILIARY eliminators. `add_inductive_core` regenerates only
        // `rec` under the consumer's replay policy, so `casesOn` / `recOn` are
        // carried as ordinary value-bearing definitions and re-typechecked by
        // the loader's own `add_decl` (the consumer's replay-match step skips
        // them for exactly this reason, `is_auxiliary_eliminator`). Absent ones
        // are simply skipped — a HIT generates no `casesOn`.
        for suffix in ["casesOn", "recOn"] {
            let aux_name = Name::from_string(&format!("{member}.{suffix}"));
            let Some(info) = env.get_const(&aux_name) else {
                continue;
            };
            let Some(value) = info.value.as_ref() else {
                continue;
            };
            // EARNED, not asserted, and gated on the kernel's own verdict
            // rather than on the declaration's KIND: `validate_and_stamp_recursor`
            // runs `check_decl_readonly_strict` (a full type check of
            // `value : type_`) before recording `FullKernelCheck`. That is
            // the recorded verdict this family path carries; it does not run
            // the synthesized-definition emitter's additional fresh check.
            // The consumer re-checks the value. Anything short of the recorded
            // full check is the honest `Axiomatized`.
            let confidence = if env.declaration_verification(&aux_name)
                == Some(DeclarationVerification::FullKernelCheck)
            {
                ImportConfidence::KernelVerified
            } else {
                ImportConfidence::Axiomatized
            };
            rows.push(FamilyRow {
                name: aux_name.to_string(),
                decl_kind: DeclKind::Definition,
                type_: &info.type_,
                value: Some(value),
                level_params: info.level_params.iter().map(ToString::to_string).collect(),
                inductive_meta: None,
                confidence,
                ledger_note: "auxiliary eliminator generated by the kernel's checked \
                              add_inductive; value type-checked by validate_and_stamp_recursor",
            });
        }
    }
    Some(rows)
}

/// Emit the inductive FAMILIES this lane installs into the replay environment
/// (`DATATYPE_INDUCTIVE_ROOTS`, currently `Num`) to `writer`, and return how
/// many shard rows were written.
///
/// Call this in the same place and under the same bracketing as
/// [`emit_synthesized_def_consts`]: families are shared infrastructure, so a
/// per-range `.mathverse` must carry them exactly like the definitional
/// prelude (`ShardRecorder::record_shared_consts`).
///
/// # Why this exists
///
/// `register_datatype_inductives` installs `Num` through the kernel's checked
/// `add_inductive`, and the numeral embedding then references `Num`,
/// `Num.num.One/Bit0/Bit1` and `Num.rec` from the types and proof values of
/// real theorems. Those references reached the shard; the DECLARATIONS never
/// did (`emit_synthesized_def_consts` filters to value-bearing `isabelle.*`
/// definitions, and an inductive has no value). The consumer's dependency
/// loader therefore failed closed on every one of them:
///
/// ```text
/// dependency loader rejected `Num.BitM_def`: checked registration for dependency
/// `isabelle.polyinst.Num.BitM` failed: Type check error in declaration
/// isabelle.polyinst.Num.BitM: Unknown constant: Num
/// ```
///
/// # Soundness — the whole point of this function
///
/// An inductive type former, a constructor and a recursor have **no value**.
/// Nothing can "type-check their value", so nothing here may be stamped
/// [`ImportConfidence::KernelVerified`] — that stamp would be **fabricated**,
/// the precise thing `cli/parallel_verify.rs` refuses to do for these kinds
/// ("stamping them would be fabricated; `axiom_accepted` is the honest
/// verdict"). They are written at [`ImportConfidence::Axiomatized`], the same
/// tier the Lean4/Mathlib lane's `lean4::env_import::confidence_for` assigns a
/// value-less constant.
///
/// That costs nothing in citability, because admission is earned by RESIDENCY,
/// not by the tier: the consumer's `replay_inductive_family_checked` rebuilds
/// the family through the kernel's checked `Environment::add_inductive`
/// (positivity, nested positivity, universe constraints, constructor types,
/// mandatory recursor validation), byte-matches every regenerated member
/// against these rows, and only then stamps `FullKernelCheck`. Nothing on that
/// replay path reads `import_confidence` at all, and a family that fails to
/// replay stays inadmissible regardless of what tier its rows claim
/// (`can_replay_missing_dependency` refuses Inductive/Constructor/Recursor/Quot
/// unconditionally). So a fabricated stamp would buy exactly nothing — and an
/// honest one loses exactly nothing.
///
/// Every row is read back out of the kernel's own store (`get_inductive` /
/// `get_constructor` / `get_recursor`), never from the pre-`add_inductive`
/// declaration, so what the consumer byte-matches is what the kernel accepted.
pub(super) fn emit_inductive_families(
    env: &Environment,
    writer: &mut ShardWriter,
    out: &mut PureVerifiedImport,
) -> usize {
    let mut roots: Vec<&str> = DATATYPE_INDUCTIVE_ROOTS.to_vec();
    roots.sort_unstable();
    roots.dedup();

    let mut written = 0usize;
    for root in roots {
        // Fail closed: a family the kernel's side tables cannot fully resolve
        // emits nothing at all rather than a partial (silently unreplayable)
        // skeleton.
        let Some(rows) = stage_family(env, root) else {
            continue;
        };
        for row in rows {
            let name_idx = writer.add_string(&row.name);
            let type_idx = lower_kernel_expr(row.type_, writer);
            let value_idx = match row.value {
                Some(v) => lower_kernel_expr(v, writer),
                None => NO_VALUE,
            };
            let level_refs: Vec<&str> = row.level_params.iter().map(String::as_str).collect();
            let level_params_start = writer.add_string_block(&level_refs);
            let mut header = MathverseConstantHeader {
                name_idx,
                type_idx,
                value_idx,
                source_system: SourceSystem::Isabelle as u8,
                import_confidence: row.confidence as u8,
                content_domain: ContentDomain::Logic as u8,
                decl_kind: row.decl_kind as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start,
                level_params_count: u16::try_from(level_refs.len()).unwrap_or(0),
                _pad2: [0u8; 26],
            };
            // The typed `_pad2` block is what lets the consumer rebuild a
            // parameterized/mutual family through checked `add_inductive`
            // rather than treat the row as a bare skeleton.
            if let Some((num_params, all_names)) = row.inductive_meta.as_ref() {
                header.set_inductive_decl_num_params(*num_params);
                if let Ok(count) = u16::try_from(all_names.len()) {
                    if count > 0 {
                        let refs: Vec<&str> = all_names.iter().map(String::as_str).collect();
                        let start = writer.add_string_block(&refs);
                        header.set_inductive_decl_all_names(start, count);
                    }
                }
            }
            let shard_idx = writer.add_constant(header);
            out.written_constants.push(WrittenConstant {
                name: row.name,
                shard_idx,
                confidence: row.confidence as u8,
                ledger_note: Some(row.ledger_note.to_string()),
            });
            written += 1;
        }
    }
    written
}

#[cfg(test)]
mod tests {
    use super::super::super::isabelle_pure_translate::register_datatype_inductives;
    use super::*;
    use clean_kernel::{Declaration, Expr};

    /// A replay environment with the lane's datatype inductives installed, i.e.
    /// exactly what the three drivers hold when they call the emitter.
    fn env_with_datatypes() -> Environment {
        let mut env = Environment::with_prelude();
        register_datatype_inductives(&mut env);
        env
    }

    /// `(name, decl_kind, confidence, has_value)` for every emitted row.
    fn emitted_rows(env: &Environment) -> Vec<(String, u8, u8, bool)> {
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let n = emit_inductive_families(env, &mut writer, &mut out);
        assert_eq!(
            n,
            out.written_constants.len(),
            "every emitted row must be a recorded write (the shard round-trip \
             asserts constant_count == written_constants.len())"
        );
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("shard read");
        out.written_constants
            .iter()
            .map(|w| {
                let h = &reader.constants[w.shard_idx as usize];
                (
                    w.name.clone(),
                    h.decl_kind,
                    h.import_confidence,
                    h.value_idx != NO_VALUE,
                )
            })
            .collect()
    }

    #[test]
    fn test_emit_inductive_families_writes_the_full_num_skeleton() {
        let env = env_with_datatypes();
        let rows = emitted_rows(&env);
        let shape: Vec<(&str, u8)> = rows.iter().map(|(n, k, _, _)| (n.as_str(), *k)).collect();
        assert_eq!(
            shape,
            vec![
                ("Num", DeclKind::Inductive as u8),
                // DECLARATION order, not name-ascending: the consumer derives
                // constructor order from the shard's `Num.rec`, and a permuted
                // order would regenerate a recursor with permuted minors.
                ("Num.num.One", DeclKind::Constructor as u8),
                ("Num.num.Bit0", DeclKind::Constructor as u8),
                ("Num.num.Bit1", DeclKind::Constructor as u8),
                ("Num.rec", DeclKind::Recursor as u8),
                ("Num.casesOn", DeclKind::Definition as u8),
                ("Num.recOn", DeclKind::Definition as u8),
            ],
            "the emitted family is exactly the row set \
             `replay_inductive_family_checked` reads"
        );
    }

    /// THE soundness invariant of this module: an inductive type former, a
    /// constructor and a recursor have no value, so nothing can type-check
    /// their value — a `KernelVerified` stamp on them would be fabricated.
    #[test]
    fn test_emit_inductive_families_never_stamps_a_valueless_row_kernel_verified() {
        let env = env_with_datatypes();
        for (name, kind, confidence, has_value) in emitted_rows(&env) {
            if !has_value {
                assert_ne!(
                    confidence,
                    ImportConfidence::KernelVerified as u8,
                    "`{name}` is value-less; a KernelVerified stamp would be fabricated"
                );
                assert_eq!(
                    confidence,
                    ImportConfidence::Axiomatized as u8,
                    "`{name}` must carry the honest value-less tier"
                );
            }
            if confidence == ImportConfidence::KernelVerified as u8 {
                assert!(
                    has_value,
                    "`{name}` is stamped KernelVerified without a value to check"
                );
                assert_eq!(
                    env.declaration_verification(&Name::from_string(&name)),
                    Some(DeclarationVerification::FullKernelCheck),
                    "`{name}`'s KernelVerified stamp must be the kernel's own verdict, \
                     not a function of its DeclKind"
                );
            }
            // No family row may claim an axiom-bearing profile it did not earn.
            let _ = kind;
        }
    }

    #[test]
    fn test_emit_inductive_families_root_list_matches_what_is_registered() {
        let env = env_with_datatypes();
        for root in DATATYPE_INDUCTIVE_ROOTS {
            assert!(
                env.get_inductive(&Name::from_string(root)).is_some(),
                "`{root}` is declared emittable but `register_datatype_inductives` \
                 does not install it — the two sides have drifted"
            );
        }
    }

    /// Fail closed: a root the kernel's side tables do not know emits nothing,
    /// rather than a partial family (one bad row makes the consumer decline the
    /// WHOLE family, converting a loud failure into a silent one).
    #[test]
    fn test_emit_inductive_families_unregistered_root_emits_nothing() {
        let env = Environment::with_prelude();
        assert!(
            stage_family(&env, "NoSuchDatatypeRoot").is_none(),
            "an unknown family root must stage no rows"
        );
    }

    #[test]
    fn test_emit_inductive_families_is_deterministic() {
        let env = env_with_datatypes();
        let mut w1 = ShardWriter::new();
        let mut w2 = ShardWriter::new();
        let mut o1 = PureVerifiedImport::default();
        let mut o2 = PureVerifiedImport::default();
        assert!(emit_inductive_families(&env, &mut w1, &mut o1) > 0);
        assert!(emit_inductive_families(&env, &mut w2, &mut o2) > 0);
        let mut b1 = Vec::new();
        let mut b2 = Vec::new();
        w1.write(&mut b1).expect("shard write");
        w2.write(&mut b2).expect("shard write");
        assert_eq!(b1, b2, "family emission must not depend on hash iteration");
    }

    /// The `_pad2` typed block is what lets the consumer rebuild the family
    /// through checked `add_inductive` instead of treating the row as a bare
    /// skeleton. Losing it silently reintroduces the uncitable-residue bug.
    #[test]
    fn test_emit_inductive_families_stamps_inductive_metadata() {
        let env = env_with_datatypes();
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        assert!(emit_inductive_families(&env, &mut writer, &mut out) > 0);
        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("shard read");
        let (_, header) = reader.lookup_name("Num").expect("Num header present");
        assert_eq!(header.decl_kind, DeclKind::Inductive as u8);
        assert_eq!(header.inductive_decl_num_params(), Some(0));
        let (start, count) = header
            .inductive_decl_all_names_block()
            .expect("all_names block written");
        let names: Vec<&str> = (0..count)
            .filter_map(|i| reader.strings.get((start + u32::from(i)) as usize))
            .map(String::as_str)
            .collect();
        assert_eq!(
            names,
            vec!["Num"],
            "the all_names block must be the family's own type list"
        );
    }

    #[test]
    fn test_is_serial_identity_digits_only() {
        assert!(is_serial_identity("isabelle.s532"));
        assert!(!is_serial_identity("isabelle.set.foo"));
        assert!(!is_serial_identity("isabelle.s"));
        assert!(!is_serial_identity("isabelle.def.HOL.True"));
    }

    #[test]
    fn test_emit_writes_kernel_accepted_definition_only() {
        let mut env = Environment::with_prelude();
        // A real, kernel-checked synthesized definition.
        env.add_decl(Declaration::Definition {
            name: Name::from_string("isabelle.def.Test.k"),
            level_params: Vec::new(),
            type_: Expr::prop(),
            value: Expr::const_str("True"),
            is_reducible: true,
        })
        .expect("definition kernel-checks");
        // A ledger-style axiom must never be emitted.
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("isabelle.trusted.s1"),
            level_params: Vec::new(),
            type_: Expr::prop(),
        })
        .expect("axiom registers");

        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let n = emit_synthesized_def_consts(&env, &mut writer, &mut out);
        assert_eq!(n, 1, "only the value-bearing synthesized definition emits");
        assert_eq!(out.written_constants.len(), 1);
        assert_eq!(
            out.written_constants[0].confidence,
            ImportConfidence::KernelVerified as u8
        );
    }

    /// A synthesized definition decoded from a replay snapshot is resident but
    /// carries no kernel record (the kernel serde-skips
    /// `declaration_verification`), so the strict emitter writes no row.
    /// Residency is not a kernel check.
    #[test]
    fn test_emit_decoded_definition_is_not_stamped_kernel_verified() {
        let name = Name::from_string("isabelle.def.Test.k");
        let mut env = Environment::with_prelude();
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::prop(),
            value: Expr::const_str("True"),
            is_reducible: true,
        })
        .expect("definition kernel-checks");
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );

        // The snapshot path: the whole environment through bincode, as
        // `save_snapshot` / `load_snapshot` carry it.
        let bytes = bincode::serde::encode_to_vec(&env, bincode::config::standard())
            .expect("environment encodes");
        let (decoded, _): (Environment, usize) =
            bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
                .expect("environment decodes");
        assert!(
            decoded.get_const(&name).is_some(),
            "the definition stays resident"
        );
        assert_eq!(decoded.declaration_verification(&name), None);

        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        assert_eq!(
            emit_synthesized_def_consts(&decoded, &mut writer, &mut out),
            0,
            "a decoded definition has no kernel check behind it in this run"
        );
        assert!(out.written_constants.is_empty());
        let mut bytes = Vec::new();
        writer.write(&mut bytes).expect("shard write");
        let reader = crate::shard::ShardReader::from_bytes(&bytes).expect("shard read");
        assert!(
            reader.lookup_name("isabelle.def.Test.k").is_none(),
            "no unrecorded definition may enter the emitted shard"
        );

        // Control: the same environment before the round trip stamps the
        // kernel's verdict.
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        assert_eq!(emit_synthesized_def_consts(&env, &mut writer, &mut out), 1);
        assert_eq!(
            out.written_constants[0].confidence,
            ImportConfidence::KernelVerified as u8
        );
    }

    #[test]
    fn test_emit_rechecks_checked_opaque_values() {
        let mut env = Environment::with_prelude();
        let name = Name::from_string("isabelle.def.Test.opaque");
        env.add_decl(Declaration::Opaque {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::prop(),
            value: Expr::const_str("True"),
        })
        .expect("opaque value kernel-checks");
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        assert_eq!(emit_synthesized_def_consts(&env, &mut writer, &mut out), 1);
        let mut bytes = Vec::new();
        writer.write(&mut bytes).expect("shard write");
        let reader = crate::shard::ShardReader::from_bytes(&bytes).expect("shard read");
        let header = &reader.constants[out.written_constants[0].shard_idx as usize];
        assert_eq!(header.decl_kind, DeclKind::Opaque as u8);
        assert_eq!(
            header.import_confidence,
            ImportConfidence::KernelVerified as u8
        );
        assert_ne!(header.value_idx, NO_VALUE);
    }

    #[test]
    fn test_emit_does_not_upgrade_structural_definitions() {
        let mut env = Environment::with_prelude();
        env.add_decl(Declaration::Definition {
            name: Name::from_string("isabelle.def.Test.checked"),
            level_params: Vec::new(),
            type_: Expr::prop(),
            value: Expr::const_str("True"),
            is_reducible: true,
        })
        .expect("checked positive registers");
        for (suffix, value, type_checks) in [
            ("structural_valid", Expr::const_str("True"), true),
            ("structural_invalid", Expr::const_str("Nat.zero"), false),
        ] {
            let name = Name::from_string(&format!("isabelle.def.Test.{suffix}"));
            let declaration = Declaration::Definition {
                name: name.clone(),
                level_params: Vec::new(),
                type_: Expr::prop(),
                value,
                is_reducible: true,
            };
            env.add_decl_structural(declaration.clone())
                .expect("the genuine structural path admits this fixture");
            assert_eq!(
                env.declaration_verification(&name),
                Some(DeclarationVerification::StructuralOnly)
            );
            assert_eq!(
                env.check_decl_readonly_strict(&declaration).is_ok(),
                type_checks
            );
        }
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        assert_eq!(emit_synthesized_def_consts(&env, &mut writer, &mut out), 1);
        assert_eq!(out.written_constants.len(), 1);
        assert_eq!(out.written_constants[0].name, "isabelle.def.Test.checked");
    }

    #[test]
    fn test_emit_rechecks_a_stale_checked_dependency_context() {
        let mut env = Environment::with_prelude();
        let dependency = Name::from_string("EmitterDependency");
        env.add_decl(Declaration::Definition {
            name: dependency.clone(),
            level_params: Vec::new(),
            type_: Expr::prop(),
            value: Expr::const_str("True"),
            is_reducible: true,
        })
        .expect("dependency kernel-checks");
        let name = Name::from_string("isabelle.def.Test.dependent");
        let declaration = Declaration::Definition {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::prop(),
            value: Expr::const_(dependency.clone(), Vec::new()),
            is_reducible: true,
        };
        env.add_decl(declaration.clone())
            .expect("dependent kernel-checks");
        assert!(env.forget_decl(&dependency));
        env.add_decl_structural(Declaration::Axiom {
            name: dependency,
            level_params: Vec::new(),
            type_: Expr::const_str("Nat"),
        })
        .expect("changed dependency structurally registers");
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck),
            "the target's actual old admission flag survives dependency replacement"
        );
        assert!(env.check_decl_readonly_strict(&declaration).is_err());
        let mut writer = ShardWriter::new();
        let mut out = PureVerifiedImport::default();
        let mut before = Vec::new();
        writer.write(&mut before).expect("initial writer snapshot");
        assert_eq!(emit_synthesized_def_consts(&env, &mut writer, &mut out), 0);
        assert!(out.written_constants.is_empty());
        let mut after = Vec::new();
        writer.write(&mut after).expect("final writer snapshot");
        assert_eq!(
            before, after,
            "a rejected candidate must not intern writer data"
        );
    }

    #[test]
    fn test_emit_is_name_sorted_and_deterministic() {
        let mut env = Environment::with_prelude();
        for n in ["isabelle.def.B", "isabelle.def.A", "isabelle.polyinst.C"] {
            env.add_decl(Declaration::Definition {
                name: Name::from_string(n),
                level_params: Vec::new(),
                type_: Expr::prop(),
                value: Expr::const_str("True"),
                is_reducible: true,
            })
            .expect("definition kernel-checks");
        }
        let mut w1 = ShardWriter::new();
        let mut w2 = ShardWriter::new();
        let mut o1 = PureVerifiedImport::default();
        let mut o2 = PureVerifiedImport::default();
        assert_eq!(emit_synthesized_def_consts(&env, &mut w1, &mut o1), 3);
        assert_eq!(emit_synthesized_def_consts(&env, &mut w2, &mut o2), 3);
        let mut b1 = Vec::new();
        let mut b2 = Vec::new();
        w1.write(&mut b1).expect("shard write");
        w2.write(&mut b2).expect("shard write");
        assert_eq!(b1, b2, "emission order must not depend on hash iteration");
    }
}
