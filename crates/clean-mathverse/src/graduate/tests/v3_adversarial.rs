// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Part of `graduate::tests` — spliced into tests/mod.rs via `include!` so
// every test keeps its pre-split `graduate::tests::*` fully-qualified name.
// v3 adversarial vectors (design §6 surfaces a1–a3 + fence): forged family
// metadata, smuggled value-less constants, recursor swaps, tampered
// carried_inductives sections, mutual families smuggled as single-type.

/// Forged `carried_inductives` entry claiming the family-checked
/// KernelVerified verdict and a foundational-only closure, no matter what
/// the shard actually contains.
fn forged_family_entry(
    root: &str,
    root_type: &Expr,
    ctors: &[(&str, &Expr)],
    extra_members: &[(&str, &str, &Expr)],
    required_by: &[&str],
) -> CarriedInductive {
    let mut members = vec![CarriedInductiveMember {
        name: root.to_string(),
        decl_kind: "inductive".to_string(),
        statement_hash: expr_canonical_digest(root_type).expect("hash root"),
    }];
    for (name, type_) in ctors {
        members.push(CarriedInductiveMember {
            name: (*name).to_string(),
            decl_kind: "constructor".to_string(),
            statement_hash: expr_canonical_digest(type_).expect("hash ctor"),
        });
    }
    for (name, kind, type_) in extra_members {
        members.push(CarriedInductiveMember {
            name: (*name).to_string(),
            decl_kind: (*kind).to_string(),
            statement_hash: expr_canonical_digest(type_).expect("hash member"),
        });
    }
    CarriedInductive {
        name: root.to_string(),
        level_params: Vec::new(),
        num_params: 0,
        statement_hash: expr_canonical_digest(root_type).expect("hash root"),
        constructors: ctors
            .iter()
            .map(|(name, type_)| CarriedInductiveConstructor {
                name: (*name).to_string(),
                statement_hash: expr_canonical_digest(type_).expect("hash ctor"),
            })
            .collect(),
        members_in_shard: members,
        kernel: KernelFacts {
            verdict: KernelVerdict::KernelVerified, // the lie
            value_typechecked: false,
            family_checked: true, // the lie
            checker: "forged".to_string(),
        },
        axiom_closure: AxiomClosure {
            foundational_only: true, // the lie
            domain_axioms: Vec::new(),
            axiom_profile_bits: 0,
        },
        structure_fields: Vec::new(),
        required_by: required_by.iter().map(|s| (*s).to_string()).collect(),
    }
}

/// Build a forged Cake shard containing family members + one genuine
/// theorem, with a fully self-consistent forged v3 record and correctly
/// re-forged digest bindings. Returns the shard path.
fn forge_family_shard(
    dir: &Path,
    members: &[InductiveFamilyMemberExport<'_>],
    families: Vec<CarriedInductive>,
    family_roots: &[&str],
) -> PathBuf {
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let member_indices = builder
        .add_inductive_family(0, members)
        .expect("forged family export");
    let thm_idx = builder
        .add_declaration(&theorem(IMP_SELF, imp_self_type(), imp_self_value()), &[])
        .expect("forged thm export");
    builder
        .shard_writer_mut()
        .set_constant_axiom_profile(thm_idx, crate::types::AxiomProfile::NONE);
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION);
    let mut thm_entry = forged_accepted_entry(IMP_SELF, &imp_self_type(), &imp_self_value(), &[]);
    thm_entry.carried_inductives = family_roots.iter().map(|s| (*s).to_string()).collect();
    record.theorems = vec![thm_entry];
    record.carried_inductives = families;
    record.result.accepted = vec![IMP_SELF.to_string()];

    let mut constants: Vec<(u32, &str)> = member_indices
        .into_iter()
        .zip(members.iter().map(|m| m.name))
        .collect();
    constants.push((thm_idx, IMP_SELF));
    let shard_path = dir.join("forged-graduated.mathverse");
    forge_bindings_and_write(&mut builder, &mut record, &constants, &shard_path);
    shard_path
}

/// Like [`forge_family_shard`] but stamps the record's `recheck_base` as
/// `lean-core`, so the cake gate replays the family through
/// `add_inductive_core` (which regenerates the type, constructors, and `rec` —
/// but NOT the value-bearing auxiliary eliminators `casesOn`/`recOn`).
fn forge_lean_core_family_shard(
    dir: &Path,
    members: &[InductiveFamilyMemberExport<'_>],
    families: Vec<CarriedInductive>,
    family_roots: &[&str],
) -> PathBuf {
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Cake);
    let member_indices = builder
        .add_inductive_family(0, members)
        .expect("forged family export");
    let thm_idx = builder
        .add_declaration(&theorem(IMP_SELF, imp_self_type(), imp_self_value()), &[])
        .expect("forged thm export");
    builder
        .shard_writer_mut()
        .set_constant_axiom_profile(thm_idx, crate::types::AxiomProfile::NONE);
    builder.shard_writer_mut().finalize_axiom_profiles();

    let mut record = forged_record_skeleton(GRADUATION_SCHEMA_VERSION);
    record.gate.recheck_base = "lean-core".to_string();
    let mut thm_entry = forged_accepted_entry(IMP_SELF, &imp_self_type(), &imp_self_value(), &[]);
    thm_entry.carried_inductives = family_roots.iter().map(|s| (*s).to_string()).collect();
    record.theorems = vec![thm_entry];
    record.carried_inductives = families;
    record.result.accepted = vec![IMP_SELF.to_string()];

    let mut constants: Vec<(u32, &str)> = member_indices
        .into_iter()
        .zip(members.iter().map(|m| m.name))
        .collect();
    constants.push((thm_idx, IMP_SELF));
    let shard_path = dir.join("forged-lean-core-graduated.mathverse");
    forge_bindings_and_write(&mut builder, &mut record, &constants, &shard_path);
    shard_path
}

#[test]
fn test_cake_gate_rejects_forged_aux_eliminator_recursor_lean_core() {
    // ADVERSARIAL (recOn/casesOn launder): under the lean-core base,
    // `add_inductive_core` regenerates the inductive type, its constructors,
    // and `rec` — but NOT the value-bearing auxiliary eliminators
    // `casesOn`/`recOn`. `checked_inductive_replay_matches_shard` legitimately
    // SKIPS those absent aux eliminators (they arrive as value-checked
    // `carried_definitions`, re-typechecked by `replay_constant`'s `add_decl`;
    // they are never legitimate name-trusted family members under this base).
    //
    // The bug: the standalone family root seeded `families.verified` from the
    // RAW `generated_names` — which unconditionally include `.recOn`/`.casesOn`
    // regardless of what the kernel regenerated. So a forged shard constant
    // named `W.recOn` declared as `DeclKind::Recursor`, with an ARBITRARY type
    // checked NOWHERE, sailed through the non-root member branch on name
    // membership alone and retained `ImportConfidence::KernelVerified`. The fix
    // seeds `families.verified` only with members the kernel actually
    // re-derived into `env`, so the forgery fails closed with
    // `CarriedFamilyMismatch`.
    let mut scratch = Environment::new();
    add_w_family(&mut scratch);
    let real = |name: &str| {
        scratch
            .get_const(&Name::from_string(name))
            .expect("member in scratch env")
            .clone()
    };
    let (root_info, mk_info, rec_info) = (real(W_FAM), real(W_MK), real(W_REC));
    let rec_on = "GradPilot.W.recOn";
    // A blatantly wrong "type" for recOn (the genuine recursor type is a large
    // Pi telescope). Its truth is irrelevant: the exploit is that NOTHING
    // checks it. If accepted, `W.recOn : W` would be laundered to KernelVerified.
    let forged_rec_on_ty = Expr::const_str(W_FAM);

    let tmp = tempfile::tempdir().expect("tempdir");
    let members = [
        InductiveFamilyMemberExport {
            name: W_FAM,
            decl_kind: DeclKind::Inductive,
            level_params: &root_info.level_params,
            type_: &root_info.type_,
        },
        InductiveFamilyMemberExport {
            name: W_MK,
            decl_kind: DeclKind::Constructor,
            level_params: &mk_info.level_params,
            type_: &mk_info.type_,
        },
        InductiveFamilyMemberExport {
            name: W_REC,
            decl_kind: DeclKind::Recursor,
            level_params: &rec_info.level_params,
            type_: &rec_info.type_,
        },
        InductiveFamilyMemberExport {
            name: rec_on, // forged auxiliary eliminator, smuggled as a recursor
            decl_kind: DeclKind::Recursor,
            level_params: &[],
            type_: &forged_rec_on_ty,
        },
    ];
    let family = forged_family_entry(
        W_FAM,
        &root_info.type_,
        &[(W_MK, &mk_info.type_)],
        &[
            (W_REC, "recursor", &rec_info.type_),
            (rec_on, "recursor", &forged_rec_on_ty),
        ],
        &[IMP_SELF],
    );
    let shard_path = forge_lean_core_family_shard(tmp.path(), &members, vec![family], &[W_FAM]);

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        !report.is_clean(),
        "a forged aux-eliminator recursor must fail the lean-core cake gate: {:?}",
        report.violations
    );
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            CakeGateViolation::CarriedFamilyMismatch { name, .. } if name == rec_on
        )),
        "the forged `{rec_on}` must fail closed — it is never regenerated by \
         add_inductive_core and so must never be family-verified: {:?}",
        report.violations
    );
    // The GENUINE family members must replay cleanly: the fix rejects only the
    // unverified aux-eliminator forgery, not the legitimately-replayed family.
    assert!(
        !report.violations.iter().any(|v| matches!(
            v,
            CakeGateViolation::CarriedFamilyMismatch { name, .. }
                | CakeGateViolation::KernelRejected { name, .. }
                if name == W_FAM || name == W_MK || name == W_REC
        )),
        "the genuine W family members must replay cleanly under lean-core: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_forged_family_positivity_smuggle() {
    // ADVERSARIAL (a3): an unsound inductive — negative occurrence of the
    // type in its own constructor — written straight into a Cake shard with
    // fully self-consistent forged paperwork. The gate's checked
    // `add_inductive` replay (the same checker that guards the prelude) must
    // reject it; paperwork can never launder positivity.
    const BAD: &str = "GradPilot.BadNeg";
    const BAD_MK: &str = "GradPilot.BadNeg.mk";

    let tmp = tempfile::tempdir().expect("tempdir");
    let bad_ty = type_sort();
    // mk : (BadNeg → Prop) → BadNeg — BadNeg occurs negatively.
    let bad_mk_ty = Expr::pi(
        bd(),
        Expr::pi(bd(), Expr::const_str(BAD), Expr::prop()),
        Expr::const_str(BAD),
    );
    let members = [
        InductiveFamilyMemberExport {
            name: BAD,
            decl_kind: DeclKind::Inductive,
            level_params: &[],
            type_: &bad_ty,
        },
        InductiveFamilyMemberExport {
            name: BAD_MK,
            decl_kind: DeclKind::Constructor,
            level_params: &[],
            type_: &bad_mk_ty,
        },
    ];
    let family = forged_family_entry(BAD, &bad_ty, &[(BAD_MK, &bad_mk_ty)], &[], &[IMP_SELF]);
    let shard_path = forge_family_shard(tmp.path(), &members, vec![family], &[BAD]);

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        !report.is_clean(),
        "positivity smuggle must fail the family replay clause"
    );
    assert!(
        report.violations.iter().any(|v| {
            matches!(v, CakeGateViolation::KernelRejected { name, .. } if name == BAD)
        }),
        "the kernel's add_inductive must reject the negative occurrence: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_forged_family_dropped_constructor() {
    // ADVERSARIAL (a1): drop a constructor from the shard. The replay
    // rebuilds the family from the shard's own constants — a 1-constructor
    // decl — so the regenerated `.rec` has one minor premise while the
    // shard's `.rec` (harvested from the REAL 2-constructor family) has two:
    // CarriedFamilyMismatch, fail-closed.
    const B2: &str = "GradPilot.B2";
    const B2_T: &str = "GradPilot.B2.t";
    const B2_F: &str = "GradPilot.B2.f";
    const B2_REC: &str = "GradPilot.B2.rec";

    let mut scratch = Environment::new();
    scratch
        .add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(B2),
                type_: type_sort(),
                constructors: vec![
                    IndConstructor {
                        name: Name::from_string(B2_T),
                        type_: Expr::const_str(B2),
                    },
                    IndConstructor {
                        name: Name::from_string(B2_F),
                        type_: Expr::const_str(B2),
                    },
                ],
            }],
        })
        .expect("genuine 2-constructor family must kernel-check");
    let real = |name: &str| {
        scratch
            .get_const(&Name::from_string(name))
            .expect("member in scratch env")
            .clone()
    };
    let (root_info, t_info, rec_info) = (real(B2), real(B2_T), real(B2_REC));

    let tmp = tempfile::tempdir().expect("tempdir");
    let members = [
        InductiveFamilyMemberExport {
            name: B2,
            decl_kind: DeclKind::Inductive,
            level_params: &root_info.level_params,
            type_: &root_info.type_,
        },
        // B2.f deliberately omitted.
        InductiveFamilyMemberExport {
            name: B2_T,
            decl_kind: DeclKind::Constructor,
            level_params: &t_info.level_params,
            type_: &t_info.type_,
        },
        InductiveFamilyMemberExport {
            name: B2_REC,
            decl_kind: DeclKind::Recursor,
            level_params: &rec_info.level_params,
            type_: &rec_info.type_,
        },
    ];
    let family = forged_family_entry(
        B2,
        &root_info.type_,
        &[(B2_T, &t_info.type_)],
        &[(B2_REC, "recursor", &rec_info.type_)],
        &[IMP_SELF],
    );
    let shard_path = forge_family_shard(tmp.path(), &members, vec![family], &[B2]);

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        !report.is_clean(),
        "a dropped constructor must fail the member cross-check"
    );
    assert!(
        report.violations.iter().any(|v| {
            matches!(v, CakeGateViolation::CarriedFamilyMismatch { name, .. } if name == B2)
        }),
        "regenerated .rec (1 minor) vs shard .rec (2 minors) must mismatch: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_forged_family_recursor_swap() {
    // ADVERSARIAL (a3 swap): the family is genuine but `W.rec`'s type bytes
    // are swapped with `W.recOn`'s (major-premise-first). The regenerated
    // recursor must byte-match the shard: CarriedFamilyMismatch.
    let mut scratch = Environment::new();
    add_w_family(&mut scratch);
    let real = |name: &str| {
        scratch
            .get_const(&Name::from_string(name))
            .expect("member in scratch env")
            .clone()
    };
    let (root_info, mk_info) = (real(W_FAM), real(W_MK));
    let rec_on_info = real("GradPilot.W.recOn");
    assert_ne!(
        real(W_REC).type_,
        rec_on_info.type_,
        "fixture sanity: rec and recOn types must differ for the swap to be a forgery"
    );

    let tmp = tempfile::tempdir().expect("tempdir");
    let members = [
        InductiveFamilyMemberExport {
            name: W_FAM,
            decl_kind: DeclKind::Inductive,
            level_params: &root_info.level_params,
            type_: &root_info.type_,
        },
        InductiveFamilyMemberExport {
            name: W_MK,
            decl_kind: DeclKind::Constructor,
            level_params: &mk_info.level_params,
            type_: &mk_info.type_,
        },
        InductiveFamilyMemberExport {
            name: W_REC, // the swap: rec's name, recOn's type
            decl_kind: DeclKind::Recursor,
            level_params: &rec_on_info.level_params,
            type_: &rec_on_info.type_,
        },
    ];
    let family = forged_family_entry(
        W_FAM,
        &root_info.type_,
        &[(W_MK, &mk_info.type_)],
        &[(W_REC, "recursor", &rec_on_info.type_)],
        &[IMP_SELF],
    );
    let shard_path = forge_family_shard(tmp.path(), &members, vec![family], &[W_FAM]);

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(!report.is_clean(), "a recursor swap must fail the gate");
    assert!(
        report.violations.iter().any(|v| {
            matches!(v, CakeGateViolation::CarriedFamilyMismatch { name, .. } if name == W_FAM)
        }),
        "swapped recursor type must mismatch the regenerated one: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_accepts_zero_constructor_inductive_family() {
    // REGRESSION (zero-ctor): Lean core `False`/`Empty`/`PEmpty` are legitimate
    // single-type, ZERO-CONSTRUCTOR inductives. When the shard declares the
    // complete family (here via the `all_names` block written by
    // `add_inductive_family`), the gate must rebuild + replay them like any
    // other family, not pre-filter them out. Before the fix,
    // `build_inductive_replay_metadata` returned `Ok(None)` for any empty-ctor
    // member → `CarriedFamilyUnsupportedShape`, which falsely blocked EVERY
    // graduated proof whose carried closure includes `False` (i.e. essentially
    // any concrete Nat/Bool comparison, which reaches `False` via
    // `noConfusion -> False.elim`). A genuine, complete zero-ctor family must be
    // ACCEPTED: the kernel replay proves it sound (no constructors to iterate;
    // the recursor has zero minor premises). Covers both `Prop` (`Sort 0`) and
    // `Type` (`Sort 1`) universes.
    let no_ctors: &[(&str, &Expr)] = &[];
    for (root, root_ty) in [
        ("GradPilot.VoidP", Expr::prop()),
        ("GradPilot.VoidT", type_sort()),
    ] {
        let rec_name = format!("{root}.rec");
        let mut scratch = Environment::new();
        scratch
            .add_inductive(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: Name::from_string(root),
                    type_: root_ty.clone(),
                    constructors: vec![], // ZERO constructors — the point of the test
                }],
            })
            .expect("a genuine zero-constructor family must kernel-check");
        let real = |name: &str| {
            scratch
                .get_const(&Name::from_string(name))
                .expect("member in scratch env")
                .clone()
        };
        let (root_info, rec_info) = (real(root), real(&rec_name));

        let tmp = tempfile::tempdir().expect("tempdir");
        let members = [
            InductiveFamilyMemberExport {
                name: root,
                decl_kind: DeclKind::Inductive,
                level_params: &root_info.level_params,
                type_: &root_info.type_,
            },
            InductiveFamilyMemberExport {
                name: rec_name.as_str(),
                decl_kind: DeclKind::Recursor,
                level_params: &rec_info.level_params,
                type_: &rec_info.type_,
            },
        ];
        // GENUINE family: the `forged_family_entry` "lie" fields
        // (KernelVerified / family_checked / foundational) are actually TRUE
        // here, so the entry is self-consistent and the checked replay must
        // accept it. `forge_family_shard` -> `add_inductive_family` writes the
        // `all_names` block, so this is a COMPLETE-family shard (which is what
        // gates the empty-ctor acceptance).
        let family = forged_family_entry(
            root,
            &root_info.type_,
            no_ctors,
            &[(rec_name.as_str(), "recursor", &rec_info.type_)],
            &[IMP_SELF],
        );
        let shard_path = forge_family_shard(tmp.path(), &members, vec![family], &[root]);

        let report = verify_cake_shard(&shard_path).expect("gate must run on the zero-ctor shard");
        assert!(
            !report.violations.iter().any(|v| matches!(
                v,
                CakeGateViolation::CarriedFamilyUnsupportedShape { name } if name == root
            )),
            "zero-ctor family `{root}` must NOT be rejected as unsupported-shape: {:?}",
            report.violations
        );
        assert!(
            !report.violations.iter().any(|v| matches!(
                v,
                CakeGateViolation::CarriedFamilyMismatch { name, .. }
                    | CakeGateViolation::KernelRejected { name, .. } if name == root
            )),
            "a genuine zero-ctor family `{root}` must pass the checked add_inductive replay: {:?}",
            report.violations
        );
        assert!(
            report.is_clean(),
            "a genuine zero-ctor family shard must be cake-gate clean: {:?}",
            report.violations
        );
    }
}

#[test]
fn test_cake_gate_rejects_valueless_constant_smuggled_as_constructor() {
    // ADVERSARIAL (a2): a free value-less constant stamped
    // `decl_kind=Constructor` to dodge the MissingValue check. Unlisted in
    // any family it fails UncarriedInductiveFamilyMember; listed in a forged
    // family's members it still fails CarriedFamilyMismatch, because the
    // checked replay never regenerates it.
    const FREE: &str = "GradPilot.free_smuggle";

    let mut scratch = Environment::new();
    add_w_family(&mut scratch);
    let real = |name: &str| {
        scratch
            .get_const(&Name::from_string(name))
            .expect("member in scratch env")
            .clone()
    };
    let (root_info, mk_info) = (real(W_FAM), real(W_MK));
    let free_ty = Expr::prop();

    for listed_in_record in [false, true] {
        let tmp = tempfile::tempdir().expect("tempdir");
        let members = [
            InductiveFamilyMemberExport {
                name: W_FAM,
                decl_kind: DeclKind::Inductive,
                level_params: &root_info.level_params,
                type_: &root_info.type_,
            },
            InductiveFamilyMemberExport {
                name: W_MK,
                decl_kind: DeclKind::Constructor,
                level_params: &mk_info.level_params,
                type_: &mk_info.type_,
            },
            InductiveFamilyMemberExport {
                name: FREE,
                decl_kind: DeclKind::Constructor,
                level_params: &[],
                type_: &free_ty,
            },
        ];
        let extra: &[(&str, &str, &Expr)] = if listed_in_record {
            &[(FREE, "constructor", &free_ty)]
        } else {
            &[]
        };
        let family = forged_family_entry(
            W_FAM,
            &root_info.type_,
            &[(W_MK, &mk_info.type_)],
            extra,
            &[IMP_SELF],
        );
        let shard_path = forge_family_shard(tmp.path(), &members, vec![family], &[W_FAM]);

        let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
        assert!(!report.is_clean(), "smuggled constant must fail the gate");
        if listed_in_record {
            assert!(
                report.violations.iter().any(|v| matches!(
                    v,
                    CakeGateViolation::CarriedFamilyMismatch { name, .. } if name == FREE
                )),
                "listed smuggle must fail the regenerated-member check: {:?}",
                report.violations
            );
        } else {
            assert!(
                report.violations.iter().any(|v| matches!(
                    v,
                    CakeGateViolation::UncarriedInductiveFamilyMember { name } if name == FREE
                )),
                "unlisted smuggle must fail family membership: {:?}",
                report.violations
            );
        }
    }
}

#[test]
fn test_cake_gate_rejects_mutual_family_smuggled_as_single_type() {
    // Fence enforcement at the GATE: two cross-referencing families written
    // as separate "single-type" families (no all_names metadata). The shared
    // reconstruction detects the mutual peer and fails the v3.0 fence.
    const XA: &str = "GradPilot.XA";
    const XA_MK: &str = "GradPilot.XA.mk";
    const XB: &str = "GradPilot.XB";
    const XB_MK: &str = "GradPilot.XB.mk";

    let tmp = tempfile::tempdir().expect("tempdir");
    let xa_ty = type_sort();
    let xb_ty = type_sort();
    let xa_mk_ty = Expr::pi(bd(), Expr::const_str(XB), Expr::const_str(XA));
    let xb_mk_ty = Expr::pi(bd(), Expr::const_str(XA), Expr::const_str(XB));
    let members = [
        InductiveFamilyMemberExport {
            name: XA,
            decl_kind: DeclKind::Inductive,
            level_params: &[],
            type_: &xa_ty,
        },
        InductiveFamilyMemberExport {
            name: XA_MK,
            decl_kind: DeclKind::Constructor,
            level_params: &[],
            type_: &xa_mk_ty,
        },
        InductiveFamilyMemberExport {
            name: XB,
            decl_kind: DeclKind::Inductive,
            level_params: &[],
            type_: &xb_ty,
        },
        InductiveFamilyMemberExport {
            name: XB_MK,
            decl_kind: DeclKind::Constructor,
            level_params: &[],
            type_: &xb_mk_ty,
        },
    ];
    let families = vec![
        forged_family_entry(XA, &xa_ty, &[(XA_MK, &xa_mk_ty)], &[], &[IMP_SELF]),
        forged_family_entry(XB, &xb_ty, &[(XB_MK, &xb_mk_ty)], &[], &[IMP_SELF]),
    ];
    let shard_path = forge_family_shard(tmp.path(), &members, families, &[XA, XB]);

    let report = verify_cake_shard(&shard_path).expect("gate must run on the forged pair");
    assert!(
        !report.is_clean(),
        "mutual families smuggled as single-type must fail the fence"
    );
    assert!(
        report.violations.iter().any(|v| matches!(
            v,
            CakeGateViolation::CarriedFamilyUnsupportedShape { name } if name == XA || name == XB
        )),
        "the v3.0 fence must reject the smuggled mutual shape: {:?}",
        report.violations
    );
}

#[test]
fn test_cake_gate_rejects_tampered_carried_inductives_record() {
    // Single-file tamper: editing the carried_inductives section (here the
    // replay-relevant num_params) must break the record's binding digest.
    let mut env = Environment::new();
    add_w_family(&mut env);
    env.add_decl(theorem(USES_W, uses_w_type(), uses_w_value()))
        .expect("uses_w must kernel-check");

    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("out");
    let record = graduate(
        &env,
        &names(&[USES_W]),
        &pilot_request(),
        &GraduationBaseline::empty(),
        &out,
    )
    .expect("graduation runs");
    let shard_path = out.join(&record.result.shard_filename);
    let record_path = graduation_record_path(&shard_path);

    let mut tampered = GraduationRecord::from_file(&record_path).expect("read record");
    tampered.carried_inductives[0].num_params = 7;
    tampered
        .write_to_file(&record_path)
        .expect("write tampered record");

    let report = verify_cake_shard(&shard_path).expect("gate runs on tampered record");
    assert!(
        report
            .violations
            .iter()
            .any(|v| matches!(v, CakeGateViolation::MissingGraduationNote { .. })),
        "tampered carried_inductives entry must break the binding digest; violations: {:?}",
        report.violations
    );
}
