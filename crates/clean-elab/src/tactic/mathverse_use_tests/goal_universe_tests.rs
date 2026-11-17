// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker};
use clean_mathverse::export::kernel_export::KernelShardBuilder;
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::shard::ShardReader;
use clean_mathverse::shard_verify::verify_native_shard;
use clean_mathverse::trust::policy::TrustPolicy;

use super::super::mathverse_use::{
    clear_mathverse_library, mathverse_apply_named, set_mathverse_library, TrustGate,
};
use super::super::ProofState;

struct LibraryGuard;

impl Drop for LibraryGuard {
    fn drop(&mut self) {
        clear_mathverse_library();
    }
}

struct TheoremFixture {
    declaration: Declaration,
    target: Expr,
    name: Name,
    goal_params: [Name; 2],
}

fn polymorphic_theorem_fixture(name: &str, depth: usize) -> TheoremFixture {
    let goal_params = [Name::from_string("goal_u"), Name::from_string("goal_v")];
    let sort_u = Expr::sort(Level::param(goal_params[0].clone()));
    let sort_v = Expr::sort(Level::param(goal_params[1].clone()));
    // forall (A : Sort u) (B : Sort v) (P : Prop), P -> P.
    let mut target = Expr::pi(
        BinderInfo::Default,
        sort_u.clone(),
        Expr::pi(
            BinderInfo::Default,
            sort_v.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
        ),
    );
    let mut value = Expr::lam(
        BinderInfo::Default,
        sort_u,
        Expr::lam(
            BinderInfo::Default,
            sort_v,
            Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
        ),
    );
    // These unused Prop binders leave both universe occurrences below the
    // old collector's depth64 cutoff without introducing an axiom.
    for _ in 0..depth {
        target = Expr::pi(BinderInfo::Default, Expr::prop(), target);
        value = Expr::lam(BinderInfo::Default, Expr::prop(), value);
    }
    let name = Name::from_string(name);
    let declaration = Declaration::Theorem {
        name: name.clone(),
        level_params: goal_params.to_vec(),
        type_: target.clone(),
        value,
    };
    TheoremFixture {
        declaration,
        target,
        name,
        goal_params,
    }
}

fn checked_library(fixture: &TheoremFixture) -> MathverseLibrary {
    let mut checked = Environment::new();
    checked
        .add_decl(fixture.declaration.clone())
        .expect("the pure polymorphic fixture must pass ordinary kernel admission");
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&fixture.declaration, &["mathverse-goal-universes"])
        .expect("export the checked polymorphic declaration");
    let directory = tempfile::tempdir().expect("polymorphic citation directory");
    let path = directory.path().join("goal-universes.mathverse");
    builder
        .write_to_file(&path)
        .expect("write the actual polymorphic shard");
    let report = verify_native_shard(&path).expect("verify the actual polymorphic shard");
    assert_eq!(
        report.checked, 1,
        "the real gate must check the declaration"
    );
    assert!(report.violations.is_empty(), "native gate: {report:?}");
    let bytes = std::fs::read(path).expect("read the verified shard");
    let shard = ShardReader::from_bytes(&bytes).expect("decode the verified shard");
    let mut library = MathverseLibrary::new(TrustPolicy::permissive());
    library
        .load_shard(&shard)
        .expect("load the real checked shard");
    library
}

fn apply_and_check(fixture: TheoremFixture, target: Expr) {
    let _guard = LibraryGuard;
    set_mathverse_library(checked_library(&fixture));
    let mut state = ProofState::new(Environment::new(), target.clone());
    let outer = Name::from_string("outer_declaration_universe");
    state.metas.add_rigid_level_param(outer.clone());
    assert!(state.metas.is_rigid_level_param(&outer));
    for param in &fixture.goal_params {
        assert!(!state.metas.is_rigid_level_param(param));
    }

    mathverse_apply_named(&mut state, &fixture.name.to_string(), TrustGate::Strict)
        .expect("strict named citation must close its actual polymorphic goal");
    assert!(state.is_complete());
    assert!(
        state.metas.is_rigid_level_param(&outer),
        "citation must retain the outer declaration's rigid parameter"
    );
    for param in &fixture.goal_params {
        assert!(
            state.metas.is_rigid_level_param(param),
            "citation must pin every goal universe: {param}"
        );
    }
    let proof = state
        .closed_proof()
        .expect("extract the actual closed proof");
    let checker = TypeChecker::new(&state.env);
    let inferred = checker
        .infer_type(&proof)
        .expect("kernel-check the cited proof");
    assert!(checker.is_def_eq(&inferred, &target));
}

#[test]
fn named_apply_pins_wrapped_goal_universes_and_keeps_outer_rigidity() {
    let fixture = polymorphic_theorem_fixture("MathverseGoalUniverses.wrapped", 0);
    let target = Expr::mdata(vec![], fixture.target.clone());
    apply_and_check(fixture, target);
}

#[test]
fn named_apply_pins_deep_goal_universes_and_keeps_outer_rigidity() {
    let fixture = polymorphic_theorem_fixture("MathverseGoalUniverses.deep", 72);
    let target = fixture.target.clone();
    apply_and_check(fixture, target);
}
