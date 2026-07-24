// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS17 — the import-verification prelude and structure-field-count soundness
//! pins.
//!
//! ## What WS17 fixes
//!
//! The kernel ships hand-rolled, NON-Lean-faithful `extends`-structure stubs in
//! its default prelude (`Preorder`/`PartialOrder`/`LinearOrder`, plus the
//! `Semigroup`→…→`CommRing` algebra hierarchy). The `Preorder.mk` stub has only
//! FOUR constructor fields — it drops Lean's trailing auto-param field
//! `lt_iff_le_not_ge` (Lean's `Preorder.mk` has FIVE). When such a stub is
//! pre-seeded, the `.olean` importer dedups by name and SKIPS the real,
//! full-fidelity Mathlib `Preorder`, so the closure keeps the lossy 4-field
//! `Preorder.mk`; every instance that applies the genuine 5th field is then
//! correctly kernel-rejected and masked to an axiom — cascading into the
//! `Order/Basic` / `Group/Defs` "Type mismatch / NotAFunction (head: Preorder)"
//! family diagnosed in WS15.
//!
//! [`Environment::try_with_prelude_for_import`] suppresses the lossy stubs so the
//! real structures register through the checked import / `add_inductive` path
//! with their full Lean field telescope.
//!
//! ## Soundness
//!
//! Suppressing the stubs makes the import prelude register STRICTLY FEWER
//! trusted constants — it can only make the kernel check the REAL declaration,
//! never let an invalid term pass. `add_inductive` still fully kernel-checks the
//! imported family (positivity, universes, recursor generation). The default
//! `with_prelude()` (kernel-internal proof scaffolding) is unchanged.

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{count_pi_args, Constructor, InductiveDecl, InductiveType};
use crate::name::Name;

/// The default prelude seeds the lossy 4-field `Preorder.mk` stub (the source of
/// the masking the import prelude must avoid).
#[test]
fn test_ws17_default_prelude_seeds_lossy_preorder_stub() {
    let env = Environment::try_with_prelude().expect("default prelude");
    assert!(
        !env.suppresses_lossy_structure_stubs(),
        "default prelude must NOT be in import-suppression mode"
    );
    let mk = env
        .get_constructor(&Name::from_string("Preorder.mk"))
        .expect("default prelude seeds the Preorder stub");
    // The hand-rolled stub historically carries 4 fields (toLE, toLT, le_refl,
    // le_trans) — it drops Lean's 5th `lt_iff_le_not_ge`. This pins the lossy
    // shape we are deliberately suppressing for import (NOT a target to "fix" by
    // padding — the real 5-field structure comes from the import).
    assert_eq!(
        mk.num_fields, 4,
        "the kernel's hand-rolled Preorder.mk stub has 4 fields"
    );
}

/// The import prelude does NOT seed `Preorder`/`PartialOrder`/`LinearOrder` or
/// the `Semigroup` algebra stub, so the real Mathlib structures register
/// canonically on import.
#[test]
fn test_ws17_import_prelude_suppresses_structure_stubs() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        env.suppresses_lossy_structure_stubs(),
        "import prelude must be in suppression mode"
    );
    for stub in [
        "Preorder",
        "Preorder.mk",
        "PartialOrder",
        "PartialOrder.mk",
        "LinearOrder",
        "Semigroup",
        "Semigroup.mk",
        "Monoid",
        "Group",
    ] {
        assert!(
            env.get_const(&Name::from_string(stub)).is_none(),
            "import prelude must NOT pre-seed the lossy stub `{stub}`"
        );
    }
    // The single-field carrier classes the structures extend (LE/LT) ARE still
    // available as foundational prelude constants — they are Lean-faithful and
    // do not shadow anything on import.
    assert!(
        env.get_const(&Name::from_string("LE")).is_some(),
        "LE must remain available in the import prelude"
    );
    assert!(
        env.get_const(&Name::from_string("LT")).is_some(),
        "LT must remain available in the import prelude"
    );
}

/// Build a faithful FIVE-field `extends`-structure (parent + four extra fields)
/// in the import prelude and confirm `add_inductive` registers its constructor
/// with `num_fields == 5` — i.e. the trailing field is NOT dropped. This is the
/// import-side behavior `try_with_prelude_for_import` unblocks for the real
/// 5-field `Preorder`.
#[test]
fn test_ws17_import_prelude_registers_full_five_field_structure() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");

    // S.{u} (a : Type u) : Type u
    let s = Name::from_string("WS17S");
    let s_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    // S.mk : (α : Type) → (f1 α) → (f2 α) → (f3 α) → (f4 α) → (f5 α) → S α
    // five genuine fields, each `α → α` (a function type), trailing f5 IMPLICIT
    // (mirroring Lean's auto-param trailing field being non-Default).
    let field_ty = |idx_from_param: u32| {
        // `α → α` where α is the binder `idx_from_param` levels out.
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(idx_from_param),
            Expr::bvar(idx_from_param + 1),
        )
    };
    let s_app = Expr::app(Expr::const_(s.clone(), vec![]), Expr::bvar(5));
    // Innermost (5th field, Implicit) -> S α
    let mut body = Expr::pi(BinderInfo::Implicit, field_ty(4), s_app);
    body = Expr::pi(BinderInfo::Default, field_ty(3), body);
    body = Expr::pi(BinderInfo::Default, field_ty(2), body);
    body = Expr::pi(BinderInfo::Default, field_ty(1), body);
    body = Expr::pi(BinderInfo::Default, field_ty(0), body);
    let mk_ty = Expr::pi(BinderInfo::Default, Expr::type_(), body);

    assert_eq!(
        count_pi_args(&mk_ty),
        6,
        "constructor telescope is 1 param + 5 fields"
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: s.clone(),
            type_: s_type,
            constructors: vec![Constructor {
                name: Name::from_string("WS17S.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("five-field structure should register through checked add_inductive");

    let mk = env
        .get_constructor(&Name::from_string("WS17S.mk"))
        .expect("WS17S.mk registered");
    assert_eq!(
        mk.num_fields, 5,
        "the FULL five-field telescope must survive add_inductive (no trailing-field drop)"
    );
    assert_eq!(mk.num_params, 1);

    // ADVERSARIAL: a constructor whose declared return type is NOT the inductive
    // being defined is a genuine mis-encoding and MUST still be rejected — the
    // fix does not weaken `add_inductive`'s checks.
    let bad = Name::from_string("WS17Bad");
    let bad_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    // Bad.mk : (α : Type) → (f : α → α) → WS17S α   (wrong head: returns S, not Bad)
    let bad_mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            field_ty(0),
            Expr::app(Expr::const_(s, vec![]), Expr::bvar(1)),
        ),
    );
    let result = env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: bad.clone(),
            type_: bad_type,
            constructors: vec![Constructor {
                name: Name::from_string("WS17Bad.mk"),
                type_: bad_mk_ty,
            }],
        }],
    });
    assert!(
        result.is_err(),
        "a constructor that does not return its own inductive must be rejected"
    );
}

// ── WS18 — `Finset` / `Fact` lossy-stub suppression ─────────────────────────
//
// The default prelude additionally hand-rolls `Finset` as a `Subtype`
// *definition* (`Finset α := { s : Multiset α // Multiset.Nodup s }`) and `Fact`
// as three opaque *axioms* (`Fact : Prop → Prop`, `Fact.out`, `Fact.mk`). Both
// shadow the genuine Mathlib structures on import: `Finset` is really a two-field
// `structure` and `Fact` a one-field `class`, each with a kernel-generated
// `.rec`. With the stub seeded, the importer dedups by name and drops the real
// inductive — so `whnf (Finset α)` delta-unfolds to `Subtype …` (breaking every
// `Finset.val`/`Finset.nodup` projection) and `Fact.rec`/`Fact.casesOn` never
// register. The same `try_with_prelude_for_import` suppression that unblocks
// `Preorder`/`Semigroup` must therefore also drop these two stubs.

/// The DEFAULT prelude seeds the lossy `Finset` (Subtype-def) and `Fact`
/// (axiom) stubs — the shapes the import prelude must avoid.
#[test]
fn test_ws18_default_prelude_seeds_lossy_finset_and_fact_stubs() {
    let env = Environment::try_with_prelude().expect("default prelude");
    assert!(
        !env.suppresses_lossy_structure_stubs(),
        "default prelude must NOT be in import-suppression mode"
    );
    // `Finset` is present as a (definition) constant, but NOT as a checked
    // inductive — i.e. the lossy Subtype carrier, which delta-unfolds.
    assert!(
        env.get_const(&Name::from_string("Finset")).is_some(),
        "default prelude seeds the Finset Subtype stub"
    );
    assert!(
        env.get_inductive(&Name::from_string("Finset")).is_none(),
        "the default Finset stub is a Subtype DEFINITION, not a real inductive"
    );
    // `Fact` is present as an axiom; its `.rec` is therefore absent.
    assert!(
        env.get_const(&Name::from_string("Fact")).is_some(),
        "default prelude seeds the Fact axiom stub"
    );
    assert!(
        env.get_const(&Name::from_string("Fact.rec")).is_none(),
        "the Fact axiom stub has no kernel-generated recursor"
    );
}

/// The import prelude does NOT seed the `Finset` Subtype-def or the `Fact`
/// axiom stub, so the real Mathlib structures (with their `.mk`/`.rec`/
/// projections) register canonically on import.
#[test]
fn test_ws18_import_prelude_suppresses_finset_and_fact_stubs() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        env.suppresses_lossy_structure_stubs(),
        "import prelude must be in suppression mode"
    );
    for stub in [
        "Finset",
        "Finset.mk",
        "Finset.val",
        "Fact",
        "Fact.out",
        "Fact.mk",
    ] {
        assert!(
            env.get_const(&Name::from_string(stub)).is_none(),
            "import prelude must NOT pre-seed the lossy stub `{stub}`"
        );
    }
    // WS19 SUPERSEDES the original WS18 note here. The `Multiset` prelude stub was
    // initially treated as Lean-faithful, but the WS19 faildump showed its
    // hand-spelled `Quot`-over-`List.Perm` carrier + `Multiset.cons`/`Mem`/… ops
    // are NOT the Mathlib `Quotient`-over-`List.isSetoid` terms, so they shadow the
    // genuine `Multiset` family on import. `Multiset` is therefore now ALSO
    // suppressed in import mode (see `test_ws19_*` below); the genuine quotient
    // `Finset`/`Multiset.Rel`/… are built over comes from the imported closure.
    // The List substrate (`List`/`List.Perm`/`List.Nodup`) the real `Multiset` is
    // built over is foundational and Lean-faithful — it stays available.
    assert!(
        env.get_const(&Name::from_string("List")).is_some(),
        "List must remain available in the import prelude"
    );
    assert!(
        env.get_const(&Name::from_string("List.Perm")).is_some(),
        "List.Perm must remain available in the import prelude"
    );
}

/// A genuine `Finset`-shaped two-field DEPENDENT structure
/// (`mk : (val : M α) → (nodup : N val) → Fin α`) registers through the checked
/// `add_inductive` path in the import prelude with a real constructor +
/// recursor, and its first-field projection types correctly — the behavior the
/// `Finset = Subtype` stub previously blocked.
#[test]
fn test_ws18_import_prelude_registers_finset_shaped_structure() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");

    // WS18Fin.{u} (α : Type u) : Type u   (one explicit param)
    let fin = Name::from_string("WS18Fin");
    let u = Name::from_string("u");
    let u_level = crate::level::Level::param(u.clone());
    let type_u = Expr::sort(crate::level::Level::succ(u_level.clone()));

    let fin_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());

    // A two-field structure where field 2's type depends on field 1, exactly like
    // Lean's `Finset` (`nodup : Nodup val`). We model field 1 as `α` and field 2
    // as `α → α` applied to the first field — a genuine dependent second field.
    //   WS18Fin.mk : {α : Type u} → (val : α) → (dep : α) → WS18Fin α
    // (the second field's *presence* and dependent typing is the point; a literal
    //  `Nodup` predicate would require pulling Multiset in, which this test
    //  deliberately avoids to stay self-contained.)
    let fin_app = Expr::app(
        Expr::const_(fin.clone(), vec![u_level.clone()]),
        Expr::bvar(2),
    );
    // innermost: (dep : α) → WS18Fin α
    let mut body = Expr::pi(BinderInfo::Default, Expr::bvar(1), fin_app);
    // (val : α) → ...
    body = Expr::pi(BinderInfo::Default, Expr::bvar(0), body);
    // {α : Type u} → ...
    let mk_ty = Expr::pi(BinderInfo::Implicit, type_u.clone(), body);

    env.add_inductive(InductiveDecl {
        level_params: vec![u.clone()],
        num_params: 1,
        types: vec![InductiveType {
            name: fin.clone(),
            type_: fin_type,
            constructors: vec![Constructor {
                name: Name::from_string("WS18Fin.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("two-field structure registers through checked add_inductive");

    let mk = env
        .get_constructor(&Name::from_string("WS18Fin.mk"))
        .expect("WS18Fin.mk registered");
    assert_eq!(
        mk.num_fields, 2,
        "both structure fields survive add_inductive"
    );
    assert_eq!(mk.num_params, 1);
    // The kernel-generated recursor MUST exist — this is exactly what the
    // `Fact.rec`/`Finset.rec` cascade was missing.
    assert!(
        env.get_const(&Name::from_string("WS18Fin.rec")).is_some(),
        "add_inductive must generate the recursor for the structure"
    );
}

// ── WS19 — `Multiset` lossy-stub suppression ────────────────────────────────
//
// The default prelude hand-rolls `Multiset` as a `def` over `Quot` with the
// relation `List.Perm` applied DIRECTLY
// (`Multiset α := @Quot (List α) (@List.Perm α)`), plus hand-spelled
// `Multiset.cons`/`Multiset.nil`/`Multiset.Mem`/`Multiset.instMembership`
// `Quot.lift`/`Quot.mk` definitions. Real Lean 4 / Mathlib `Multiset` is
// `def Multiset α := @Quotient (List α) (List.isSetoid α)` with
// `Quotient.map`/`Quotient.liftOn`-spelled ops. The carrier is *definitionally*
// the same quotient, but the stub's hand-spelled ops are NOT the Mathlib terms,
// so the loader dedups by name and SHADOWS the genuine `Multiset.*` family on
// import: 123 masked + 56 failed `Multiset.*` rows in the WS19 faildump slice,
// including `Multiset.cons.proof_1` (`heads: List vs FVar`) and 36
// `Unknown constant: Multiset.Rel`. Suppressing the stub in import mode lets the
// genuine `Multiset` family register through the checked import path
// (measured +74 KernelVerified, 0 regressions).

/// The DEFAULT prelude seeds the lossy `Multiset` (Quot-over-`List.Perm` `def`)
/// stub plus its hand-spelled ops — the shapes the import prelude must avoid.
#[test]
fn test_ws19_default_prelude_seeds_lossy_multiset_stub() {
    let env = Environment::try_with_prelude().expect("default prelude");
    assert!(
        !env.suppresses_lossy_structure_stubs(),
        "default prelude must NOT be in import-suppression mode"
    );
    // `Multiset` is present as a (reducible `Quot`-over-`List.Perm`) DEFINITION,
    // not as a real inductive — i.e. the lossy carrier that shadows the genuine
    // Mathlib `Quotient`-over-`List.isSetoid` family on import.
    assert!(
        env.get_const(&Name::from_string("Multiset")).is_some(),
        "default prelude seeds the Multiset Quot-def stub"
    );
    assert!(
        env.get_inductive(&Name::from_string("Multiset")).is_none(),
        "the default Multiset stub is a Quot DEFINITION, not a real inductive"
    );
    // Its hand-spelled ops are present too (the terms that shadow Mathlib's).
    for op in ["Multiset.cons", "Multiset.nil", "Multiset.Mem"] {
        assert!(
            env.get_const(&Name::from_string(op)).is_some(),
            "default prelude seeds the hand-spelled `{op}` stub"
        );
    }
}

/// The import prelude does NOT seed the `Multiset` Quot-def stub or its
/// hand-spelled ops, so the real Mathlib `Multiset` family registers canonically
/// on import.
#[test]
fn test_ws19_import_prelude_suppresses_multiset_stub() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        env.suppresses_lossy_structure_stubs(),
        "import prelude must be in suppression mode"
    );
    for stub in [
        "Multiset",
        "Multiset.cons",
        "Multiset.nil",
        "Multiset.Mem",
        "Multiset.instMembership",
    ] {
        assert!(
            env.get_const(&Name::from_string(stub)).is_none(),
            "import prelude must NOT pre-seed the lossy stub `{stub}`"
        );
    }
    // The `List` substrate the genuine `Multiset` quotient is built over
    // (`List` / `List.Perm`) is foundational and Lean-faithful — it stays
    // available; only the lossy `Multiset` carrier + its ops are dropped.
    assert!(
        env.get_const(&Name::from_string("List")).is_some(),
        "List must remain available in the import prelude"
    );
    assert!(
        env.get_const(&Name::from_string("List.Perm")).is_some(),
        "List.Perm must remain available in the import prelude"
    );
}

/// In the DEFAULT (proof-execution) prelude the `Multiset` stub is byte-identical
/// to before WS19 — suppression is import-only and never changes the default
/// lane. This pins the soundness invariant that `suppress_lossy_structure_stubs`
/// stays `false` by default.
#[test]
fn test_ws19_default_lane_unchanged_multiset_present() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    // Default lane: stub present. Import lane: stub absent. The two lanes diverge
    // ONLY on the lossy stub, exactly as WS17/WS18 established.
    assert!(
        default_env
            .get_const(&Name::from_string("Multiset"))
            .is_some(),
        "default lane keeps the Multiset stub (no proof-execution behavior change)"
    );
    assert!(
        import_env
            .get_const(&Name::from_string("Multiset"))
            .is_none(),
        "import lane drops the Multiset stub"
    );
}

// ── Nat arithmetic-lemma orientation-collision suppression ──────────────────
//
// The default prelude registers `Nat.succ_mul` / `Nat.mul_succ` (via
// `init_nat_arith_lemmas`) and `Nat.div_add_mod` (via `init_nat_div_mod_lemmas`)
// with the addends/factors in the OPPOSITE order to Lean 4 v4.8.0 core. Clean
// spells `Nat.succ_mul : (succ n)*m = m + n*m`, `Nat.mul_succ : n*(succ m) =
// n + n*m`, `Nat.div_add_mod : (m/n)*n + m%n = m`, whereas Lean's canonical
// statements are `(n*m)+m`, `n*m+n`, and `n*(m/n) + m%n = m`. These are genuine
// kernel-checked theorems, just non-canonically oriented. With the commuted
// forms pre-seeded, the `.olean` loader dedups by name and SHADOWS the genuine
// canonical Mathlib `Nat.*` lemmas on import, so every imported proof that
// demands the canonical orientation is correctly kernel-rejected and masked
// (`Nat.div_add_mod'` / `Nat.dvd_sub_mod` / `Nat.mul_div_eq_iff_dvd` in the
// `Mathlib/Data/Nat/Defs` faildump). Suppressing the divergent leaves + their
// dependents (`Nat.mul_comm` / `Nat.right_distrib`, built from the leaves) in
// import mode — the WS17/18/19 pattern — lets the genuine canonical lemmas
// register through the checked import path (measured Nat/Defs KV 451 → 454, 0
// regressions). The NON-divergent helpers (`Nat.add_comm`, `Nat.add_assoc`,
// `Nat.zero_add`, `Nat.succ_add`, `Nat.mul_assoc`, `Nat.left_distrib`,
// `Nat.mod_lt` — all in Lean-canonical orientation) are KEPT: their types match
// the olean so they never shadow-mask, and transitive import-prelude callers
// (`init_list_happend_inst → init_list_ops`) legitimately depend on them. The
// gate lives INSIDE `init_nat_arith_lemmas`/`init_nat_div_mod_lemmas` (not only
// at the prelude call sites) because those inits are reached through MULTIPLE
// import-prelude paths.

/// The DEFAULT prelude seeds the commuted-orientation `Nat.succ_mul` /
/// `Nat.mul_succ` / `Nat.div_add_mod` arithmetic lemmas (the shadowing shapes the
/// import prelude must avoid) plus the family members built from them.
#[test]
fn test_nat_arith_default_prelude_seeds_commuted_orientation_lemmas() {
    let env = Environment::try_with_prelude().expect("default prelude");
    assert!(
        !env.suppresses_lossy_structure_stubs(),
        "default prelude must NOT be in import-suppression mode"
    );
    for lemma in [
        "Nat.succ_mul",
        "Nat.mul_succ",
        "Nat.div_add_mod",
        "Nat.mod_lt",
        // Built constructively FROM `Nat.succ_mul` / `Nat.mul_succ` during the
        // same init — the dependents that ride the divergent-leaf suppression.
        "Nat.mul_comm",
        "Nat.right_distrib",
        // Built on top of `Nat.div_add_mod` (nn-verify IEEE754 ulp primitive).
        "Nat.ulp_universal_bound",
    ] {
        assert!(
            env.get_const(&Name::from_string(lemma)).is_some(),
            "default prelude seeds the Clean-native arithmetic lemma `{lemma}`"
        );
    }
}

/// The import prelude does NOT seed the commuted-orientation Nat arithmetic
/// lemmas (or the family members built from them), so the genuine canonical
/// Mathlib `Nat.*` lemmas register canonically through the checked import path.
#[test]
fn test_nat_arith_import_prelude_suppresses_commuted_orientation_lemmas() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        env.suppresses_lossy_structure_stubs(),
        "import prelude must be in suppression mode"
    );
    // The orientation-DIVERGENT theorems (and the family members built from
    // them) are withheld in import mode so the genuine canonical Mathlib lemmas
    // import through the checked path.
    for lemma in [
        // Leaves: Clean's addend/factor order is SWAPPED vs Lean 4 v4.8.0 core.
        "Nat.succ_mul",
        "Nat.mul_succ",
        "Nat.div_add_mod",
        // Built FROM the divergent leaves during the same init.
        "Nat.mul_comm",
        "Nat.right_distrib",
        // Built ON TOP of `Nat.div_add_mod` (Clean-native nn-verify primitive).
        "Nat.ulp_universal_bound",
    ] {
        assert!(
            env.get_const(&Name::from_string(lemma)).is_none(),
            "import prelude must NOT pre-seed the commuted-orientation lemma `{lemma}` \
             (it would shadow the genuine canonical Mathlib `{lemma}`)"
        );
    }
    // v4.30 census 2026-07-06 (pinpoint dcb769d4): the Nat CORE ARITHMETIC
    // seeds themselves (`Nat.add`/`mul`/`div`/`mod`/…) and their whole seeded
    // helper-lemma web are now import-withheld too — Lean v4.30 stores brecOn
    // towers / structural modCore / @[irreducible] WF div-mod, so every seeded
    // twin failed the import value-defeq dedup AND the fuel-peeling div/mod
    // dispatcher burned 2M-heartbeat budgets on 2^32-scale literals
    // (Char.toUpper._proof_1). See
    // test_ws_nat_core_arith_cluster_suppressed_in_import_mode for the full
    // cluster pin. Only the Nat substrate itself stays.
    for kept in [
        "Nat", "Nat.zero", "Nat.succ", "Nat.pred", "Nat.le", "Nat.lt",
    ] {
        assert!(
            env.get_const(&Name::from_string(kept)).is_some(),
            "Nat substrate `{kept}` must remain available in the import prelude"
        );
    }
}

/// In the DEFAULT (proof-execution) prelude the commuted-orientation lemmas are
/// byte-identical to before — suppression is import-only and never changes the
/// default lane the `clean check` path and every Clean-native caller
/// (`algebra_nat_mul_comm_proof`, the `boolean_analysis_*` overlays, the
/// nn-verify ulp lane) rely on. Pins the soundness invariant that the two lanes
/// diverge ONLY on the divergent leaves + their dependents.
#[test]
fn test_nat_arith_default_lane_unchanged_commuted_lemmas_present() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for lemma in ["Nat.succ_mul", "Nat.mul_succ", "Nat.div_add_mod"] {
        assert!(
            default_env.get_const(&Name::from_string(lemma)).is_some(),
            "default lane keeps the Clean-native `{lemma}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(lemma)).is_none(),
            "import lane drops the Clean-native `{lemma}`"
        );
    }
}

/// The DEFAULT (proof-execution) prelude seeds Clean's `Nat.decEq` cluster:
/// the divergent `Nat.succ_inj` overlay, the `Nat.decEq` decision procedure
/// built over it, and the concrete leaf decEq terms that dispatch on `Nat.decEq`
/// (Int / wrapper types). This is the lane `clean check`, the `decide` / `if a=b`
/// path, and every Clean-native consumer relies on — it must be UNCHANGED.
#[test]
fn test_nat_dec_eq_cluster_default_prelude_seeds_overlays() {
    let env = Environment::try_with_prelude().expect("default prelude");
    assert!(
        !env.suppresses_lossy_structure_stubs(),
        "default prelude must NOT be in import-suppression mode"
    );
    for c in [
        "Nat.succ_inj",
        "Nat.decEq",
        "instDecidableEqNat",
        "Int.decEq",
        "instDecidableEqInt",
    ] {
        assert!(
            env.get_const(&Name::from_string(c)).is_some(),
            "default prelude seeds the Clean-native decEq-cluster constant `{c}`"
        );
    }
}

/// The IMPORT prelude WITHHOLDS Clean's divergent `Nat.decEq` cluster so the
/// genuine Lean 4 v4.8.0 / Mathlib constants register through the checked import
/// path. `Nat.succ_inj` is the confirmed divergence: Clean's overlay is an
/// explicit-binder IMPLICATION, whereas genuine Mathlib `Nat.succ_inj` is an
/// IFF (`(a.succ = b.succ) ↔ (a = b)`); pre-seeding Clean's overlay shadowed the
/// genuine Iff on import (`Duplicate declaration: Nat.succ_inj`). The `Nat.decEq`
/// decision procedure (whose body references `Nat.succ_inj`) and the concrete
/// leaf decEq terms that dispatch on `Nat.decEq` ride the same suppression.
#[test]
fn test_nat_dec_eq_cluster_import_prelude_suppresses_overlays() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        env.suppresses_lossy_structure_stubs(),
        "import prelude must be in suppression mode"
    );
    for c in [
        // The confirmed-divergent leaf (implication-vs-Iff shape collision).
        "Nat.succ_inj",
        // Built over `Nat.succ_inj` — its value would reference the gated overlay.
        "Nat.decEq",
        "instDecidableEqNat",
        // Concrete leaves that dispatch on the gated `Nat.decEq`.
        "Int.decEq",
        "instDecidableEqInt",
    ] {
        assert!(
            env.get_const(&Name::from_string(c)).is_none(),
            "import prelude must NOT pre-seed the Clean-native decEq overlay `{c}` \
             (it would shadow the genuine Mathlib/Init `{c}`)"
        );
    }
    // The genuine, NON-divergent decidable-equality SUBSTRATE the imported
    // constants are stated over stays available: the `Decidable`/`DecidableEq`
    // classes, the reducible `DecidableEq` definition, and the generic `decEq`
    // bridge (all Lean-faithful in shape) must remain so the elaborator can
    // resolve `Decidable (Eq T a b)` and the imported leaf instances chain
    // through them.
    for kept in ["Decidable", "DecidableEq", "decEq", "Nat", "Int"] {
        assert!(
            env.get_const(&Name::from_string(kept)).is_some(),
            "non-divergent decidable-equality substrate `{kept}` must remain in the import prelude"
        );
    }
}

/// The two lanes diverge ONLY on the Clean-native decEq overlays: the default
/// lane keeps them (proof-execution unchanged), the import lane drops them
/// (genuine Mathlib/Init constants import unshadowed). Pins the soundness
/// invariant for the `Nat.succ_inj` → `Nat.decEq` cluster.
#[test]
fn test_nat_dec_eq_cluster_lanes_diverge_only_on_overlays() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        "Nat.succ_inj",
        "Nat.decEq",
        "instDecidableEqNat",
        "Int.decEq",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane drops the Clean-native `{c}`"
        );
    }
}

// ── WS-LEVEL: universe-arity-lossy monad/list stub suppression ──────────────
//
// The kernel ships hand-rolled `Except` (a `Type u → Type u → Type u` inductive,
// `level_params = [u]`), `List.zip` (`{α β : Type u}`, `level_params = [u]`), and
// `List.mapM` (`level_params = [u, v]`) — all monomorphic in FEWER universes than
// their Lean 4 core originals: `Except.{u, v}`, `List.zip.{u, v}`, and
// `List.mapM.{u, v, w}`. When such a stub is pre-seeded, the `.olean` importer
// dedups by name and SKIPS the genuine multi-universe declaration, so every
// imported proof that references it with the FULL level list (2 for
// `Except`/`List.zip`, 3 for `List.mapM`) is kernel-rejected with
// `LevelCountMismatch` and masked (161 rows in the mathverse-full-v2 corpus:
// 74 `Except`, 56 `List.zip`, 31 `List.mapM`). Suppressing the stubs in import
// mode — the WS17/18/19 pattern — lets the genuine constants register through the
// checked import path with their full universe telescope (measured 12-module
// sample KV 744 → 834, level_mismatch 92 → 0, 0 regressions, floor 0).
//
// SOUNDNESS: suppression makes the import prelude register STRICTLY FEWER trusted
// constants; it can only make the kernel check the REAL declaration, never let an
// invalid term pass. Nothing here touches `is_def_eq`/`whnf`. The default
// (proof-execution) lane keeps the single-universe stubs byte-identical.

/// The DEFAULT prelude seeds the single-universe `Except` / `List.zip` /
/// `List.mapM` stubs with their reduced (monomorphic) level-param arity — the
/// shapes the import prelude must avoid so the real multi-universe originals
/// register.
#[test]
fn test_ws_level_default_prelude_seeds_reduced_arity_monad_list_stubs() {
    let env = Environment::try_with_prelude().expect("default prelude");
    assert!(
        !env.suppresses_lossy_structure_stubs(),
        "default prelude must NOT be in import-suppression mode"
    );
    // Reduced-arity stubs are present with FEWER level params than Lean core.
    for (name, want_params) in [("Except", 1usize), ("List.zip", 1), ("List.mapM", 2)] {
        let ci = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("default prelude seeds the `{name}` stub"));
        assert_eq!(
            ci.level_params.len(),
            want_params,
            "default `{name}` stub is the reduced-arity ({want_params}-universe) carrier"
        );
    }
    // The `Except` constructors + monad family come with the stub.
    for op in ["Except.ok", "Except.error", "ExceptT"] {
        assert!(
            env.get_const(&Name::from_string(op)).is_some(),
            "default prelude seeds the `{op}` stub"
        );
    }
}

/// The import prelude does NOT seed the reduced-arity `Except` / `List.zip` /
/// `List.mapM` stubs (nor the `Except` monad family), so the genuine
/// multi-universe Lean originals register canonically on import.
#[test]
fn test_ws_level_import_prelude_suppresses_reduced_arity_monad_list_stubs() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        env.suppresses_lossy_structure_stubs(),
        "import prelude must be in suppression mode"
    );
    for stub in [
        "Except",
        "Except.ok",
        "Except.error",
        "ExceptT",
        "List.zip",
        "List.mapM",
    ] {
        assert!(
            env.get_const(&Name::from_string(stub)).is_none(),
            "import prelude must NOT pre-seed the reduced-arity stub `{stub}`"
        );
    }
    // The `List` substrate the genuine `List.zip`/`List.mapM` are built over stays
    // available — only the reduced-arity carriers are dropped.
    assert!(
        env.get_const(&Name::from_string("List")).is_some(),
        "List must remain available in the import prelude"
    );
}

/// In the DEFAULT (proof-execution) prelude the reduced-arity monad/list stubs are
/// byte-identical to before this gate — suppression is import-only and never
/// changes the default lane. Pins the soundness invariant that the two lanes
/// diverge ONLY on these stubs.
#[test]
fn test_ws_level_default_lane_unchanged_monad_list_stubs_present() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        "Except",
        "Except.ok",
        "Except.error",
        "List.zip",
        "List.mapM",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the reduced-arity `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane drops the reduced-arity `{c}`"
        );
    }
}

/// The String-valued `Repr` family (`reprPrec : α → Nat → String` — Lean 4.8's
/// genuine class is Format-valued) and the placeholder-bodied `ToString`
/// instances (`instToStringNat := fun _ => ""`) shadow the genuine Lean
/// declarations on `.olean` import (`WithBot.instRepr` et al. failed with
/// `expected Std.Format, got String`). In IMPORT mode both inits are
/// suppressed so the genuine Format-valued `Repr` / value-bearing `ToString`
/// instances register through the checked import path; in the DEFAULT lane
/// they are byte-identical to before the gate.
#[test]
fn test_ws_level_import_prelude_suppresses_string_repr_tostring_stubs() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        "Repr",
        "Repr.mk",
        "Repr.reprPrec",
        "repr",
        "instReprNat",
        "instReprString",
        "instReprBool",
        "instReprList",
        "ToString",
        "ToString.mk",
        "ToString.toString",
        "toString",
        "instToStringNat",
        "instToStringString",
        "instToStringBool",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the hand-rolled `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed the String-shaped stub `{c}` — it \
             shadows the genuine Lean declaration on import"
        );
    }
    // Re-pinned (v4.31 retarget, 2026-07-04): the whole v4.8 String carrier
    // (List-Char `String.mk` shape) is now import-suppressed with Char and
    // the Fin-carrier UInts — genuine v4.31 String (validated ByteArray)
    // imports through the checked path. Default lane still keeps it.
    assert!(
        default_env
            .get_const(&Name::from_string("String"))
            .is_some(),
        "default lane keeps the Clean-native String"
    );
    assert!(
        import_env.get_const(&Name::from_string("String")).is_none(),
        "import lane must NOT pre-seed the v4.8 List-Char String carrier"
    );
}

/// The Clean-native Int arithmetic cluster (`Int.add`/`Int.subNatNat`/…) is
/// NOT Lean-faithful in its SYMBOLIC reduction behaviour — `Int.subNatNat`
/// is an iterated-decrement loop (vs Lean's single case on `Nat.sub n m`),
/// so Lean-valid rfl-proofs over open Int terms (`Int.exists_strictMono`:
/// `negSucc (n+1) + 1 ≟ negSucc n`) were rejected while the stubs shadowed
/// the genuine olean definitions. In IMPORT mode the whole cluster (ops,
/// instances, `instBEqInt`, order defs, and the dependent constructive lemma
/// web) is suppressed so the genuine Lean declarations import through the
/// checked path; the DEFAULT lane keeps the stubs and their proof web
/// byte-identical.
#[test]
fn test_ws_level_import_prelude_suppresses_int_arith_cluster() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        "Int.add",
        "Int.sub",
        "Int.mul",
        "Int.subNatNat",
        "Int.beq",
        "instBEqInt",
        "Int.le",
        "Int.lt",
        "Int.subNatNat_succ_succ",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed `{c}` — it shadows the genuine \
             Lean declaration whose symbolic reduction the equation lemmas need"
        );
    }
    // The Int substrate itself (inductive + constructors + Int.neg) stays.
    for c in ["Int", "Int.ofNat", "Int.negSucc", "Int.neg"] {
        assert!(
            import_env.get_const(&Name::from_string(c)).is_some(),
            "`{c}` must remain available in the import prelude"
        );
    }
}

/// v4.31 retarget (2026-07-04): the StateT member axioms are MISSING the
/// `[Monad m]` instance binder v4.31 requires (arity drift — the incremental
/// lane's CHECKED axiom upgrade fails closed with UpgradeTypeMismatch), and
/// `Id.mk`/`IO.pure`/`IO.bind`/`StateM.pure` are phantom constants absent
/// upstream. `instBEqOption` same-name-collides with the genuine v4.31
/// derived instance with a different value (wrapping the upstream-absent
/// `Option.beq`). In IMPORT mode the five registering inits are suppressed so
/// the genuine olean declarations import; the DEFAULT lane keeps them.
#[test]
fn test_ws_level_import_prelude_suppresses_monadic_and_beq_option_stubs() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        "StateT.pure",
        "StateT.get",
        "StateT.set",
        "StateT.modify",
        "Id.mk",
        "IO.pure",
        "IO.bind",
        "StateM.pure",
        "instBEqOption",
        "Option.beq",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed `{c}` — arity-drifted/phantom/colliding \
             vs the genuine v4.31 declaration"
        );
    }
}

/// v4.31 retarget (2026-07-04), Fin/carrier round: Clean's `Fin.ofNat` pins
/// the LEAN v4.8 SIGNATURE `{n} (a : Nat) : Fin (Nat.succ n)` — v4.31 changed
/// it to `(n : Nat) → [NeZero n] → Nat → Fin n` — and `Fin.isLt` states raw
/// `Nat.lt` vs v4.31's `LT.lt` wrapper. The v4.8 Fin-carrier UInt family
/// (UInt8/16/32/64/USize, ctor wrapping `Fin size`) drifts from v4.31's
/// BitVec-based carriers, and Float + the ofNat/dec-proof webs reference
/// them. (`USize.ofNat` was dropped from the default-lane list when the
/// carrier BitVec-parity P1 reshape landed, 83b2efce — the default lane now
/// seeds an OPAQUE USize without that op.) All are import-suppressed so the genuine v4.31 declarations import;
/// the default lane keeps every one (pinned here).
#[test]
fn test_ws_level_import_prelude_suppresses_v48_fin_carrier_cluster() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let mut import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    import_env
        .init_uint_arith()
        .expect("public UInt arithmetic initializer must no-op in import mode");
    import_env
        .init_uint_arith()
        .expect("import-mode UInt arithmetic no-op must be idempotent");
    for c in [
        "Fin.ofNat",
        "Fin.isLt",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "Float",
        "UInt8.ofNat",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed `{c}` — v4.8-shape carrier/op that \
            shadows the genuine v4.31 declaration"
        );
    }
    // The wrapping arithmetic overlay and its resolver entries are inseparable
    // from those carriers. In particular, import-prelude construction must not
    // try to type-check `UInt8.add` after the carrier initializer has correctly
    // no-op'd (the former full-suite failure was `UnknownConst(UInt8)`).
    for width in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        for op in ["add", "sub", "mul"] {
            let declaration = Name::from_string(&format!("{width}.{op}"));
            assert!(
                default_env.get_const(&declaration).is_some(),
                "default lane keeps `{declaration}`"
            );
            assert!(
                import_env.get_const(&declaration).is_none(),
                "import lane must not pre-seed carrier-dependent `{declaration}`"
            );
        }
        for class in ["HAdd", "HSub", "HMul"] {
            let instance = Name::from_string(&format!("inst{class}{width}"));
            assert!(
                default_env.get_const(&instance).is_some(),
                "default lane keeps `{instance}`"
            );
            assert!(
                import_env.get_const(&instance).is_none(),
                "import lane must not pre-seed carrier-dependent `{instance}`"
            );
        }
        let of_nat = Name::from_string(&format!("instOfNat{width}"));
        assert!(
            default_env.get_const(&of_nat).is_some(),
            "default lane keeps `{of_nat}`"
        );
        assert!(
            import_env.get_const(&of_nat).is_none(),
            "import lane must not pre-seed carrier-dependent `{of_nat}`"
        );
    }
    // Char rides the same carrier gate (v4.8 Nat-shaped val vs v4.31's
    // `⟨val : UInt32, valid⟩` — instLinearOrderChar._proof_* / UInt8.toChar).
    for c in ["Char", "Char.mk", "Char.ofNat", "Char.val"] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}`"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed the v4.8-shape `{c}`"
        );
    }
    // The Fin substrate (inductive + ctor + val) stays in both lanes.
    for c in ["Fin", "Fin.mk", "Fin.val"] {
        assert!(
            import_env.get_const(&Name::from_string(c)).is_some(),
            "`{c}` must remain available in the import prelude"
        );
    }
}

/// v4.31 retarget: Clean's `Nat.sub_le_sub_left/right` are transposed-binder
/// drifted vs v4.31 (`(k : Nat)` before `h : a ≤ b`, explicit bounds, raw
/// `Nat.le` — v4.31 is `{n m} → h → (k)` in `LE.le` form; rejected
/// `Filter.map_sub_atTop_eq_nat`), and `Nat.sub_lt`'s proof value applies
/// `sub_le_sub_left` so it rides the same gate. Import lane drops all three
/// (genuine olean lemmas import); default lane keeps them.
#[test]
fn test_ws_level_import_prelude_suppresses_transposed_nat_sub_order_lemmas() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in ["Nat.sub_le_sub_left", "Nat.sub_le_sub_right", "Nat.sub_lt"] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}`"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed the transposed `{c}`"
        );
    }
    // v4.30 census 2026-07-06: the rest of the nat-sub-order family is stated
    // over the now import-gated `Nat.sub` seed (Nat core arithmetic cluster,
    // see data_types_nat.rs::init_nat), so it is withheld with it — the
    // genuine olean lemmas import through the checked path. The default lane
    // keeps every member.
    for c in ["Nat.succ_sub_succ", "Nat.pred_le_pred", "Nat.sub_self"] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}`"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed `{c}` (stated over the gated Nat.sub)"
        );
    }
}

/// v4.31 retarget: genuine v4.31 `Bool.xor` is `bne`-based — Clean's
/// `Bool.rec`-based value is delta-incompatible, and the Clean-native Nat
/// bitwise web (div2/testBit/bitwise + par helpers + their proof families)
/// both references it and shadows the genuine v4.31 bodies the
/// Mathlib.Data.Nat.Bitwise lemma family reduces through. All are
/// import-suppressed; the default lane keeps every one.
#[test]
fn test_ws_level_import_prelude_suppresses_bool_xor_nat_bitwise_cluster() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in ["Bool.xor", "Nat.div2", "Nat.bitwise", "Bool.xor_comm"] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}`"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed the drifted `{c}`"
        );
    }
    // `Nat.testBit` stays as init_nat's VALUE-LESS axiom in the import lane —
    // the genuine olean definition upgrades it through the checked path; the
    // drifted value-bearing re-registration (register_nat_testbit_def) is the
    // gated one and must not have installed a value.
    let import_testbit = import_env
        .get_const(&Name::from_string("Nat.testBit"))
        .expect("import lane keeps the upgradeable Nat.testBit axiom");
    assert!(
        import_testbit.value.is_none(),
        "import-lane Nat.testBit must be VALUE-LESS (upgradeable axiom), not          the drifted value-bearing definition"
    );
    // Bool substrate + the and/or comm proofs stay in both lanes.
    for c in [
        "Bool",
        "Bool.and",
        "Bool.or",
        "Bool.not",
        "Bool.and_comm",
        "Bool.or_comm",
    ] {
        assert!(
            import_env.get_const(&Name::from_string(c)).is_some(),
            "`{c}` must remain available in the import prelude"
        );
    }
}

/// v4.31 retarget: Clean's `Nat.decLe`/`Nat.decLt` values are Nat.rec
/// dispatcher bridges — genuine v4.31 uses `Nat.ble`-based `dite` bodies, and
/// `Decidable` is Type-valued so conversion must genuinely unfold them
/// (`Rat.instEncodable` rejected through `Subtype.encodable`'s
/// `instDecidableAnd (Nat.decLt 0 _) …` chain). Import lane drops the pair and
/// their `instDecidableNat{Lt,Le}` wrappers; default lane keeps all four.
#[test]
fn test_ws_level_import_prelude_suppresses_nat_decidable_ord_stubs() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        "Nat.decLe",
        "Nat.decLt",
        "instDecidableNatLt",
        "instDecidableNatLe",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}`"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed the drifted `{c}`"
        );
    }
    // Decidable itself stays in both lanes. (`Nat.ble` — formerly the "genuine
    // leaf" here — is import-withheld since the v4.30-census Nat core
    // arithmetic cluster gate: Clean's double-Nat.rec spelling fails the
    // value-defeq dedup against Lean's brecOn tower; the genuine olean
    // `Nat.ble` imports through the checked path instead.)
    assert!(
        import_env
            .get_const(&Name::from_string("Decidable"))
            .is_some(),
        "`Decidable` must remain available in the import prelude"
    );
    assert!(
        import_env
            .get_const(&Name::from_string("Nat.ble"))
            .is_none(),
        "import lane must NOT pre-seed `Nat.ble` (Nat core arithmetic cluster)"
    );
}

/// v4.31 retarget: Clean seeds `WellFounded.fixF`/`fix` as REDUCIBLE, so the
/// import-lane whnf digs into `Acc.rec` where genuine v4.31 keeps them folded
/// — the `PFun.fixInduction` family rejected on a proof-irrelevance-modulo-
/// congruence core (adversarially verified NOT a kernel gap). Import lane
/// drops the pair (genuine Init.WF imports with true hints); the Acc/
/// WellFounded substrate stays in both lanes.
#[test]
fn test_ws_level_import_prelude_suppresses_reducible_wf_fix_stubs() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in ["WellFounded.fixF", "WellFounded.fix"] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}`"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed the reducible `{c}`"
        );
    }
    for c in ["Acc", "Acc.rec", "WellFounded", "WellFounded.intro"] {
        assert!(
            import_env.get_const(&Name::from_string(c)).is_some(),
            "`{c}` must remain available in the import prelude"
        );
    }
}

/// v4.31 retarget: Clean's seeded `Subtype.mk/val/property` carry the
/// predicate binder EXPLICITLY (genuine v4.31: implicit), shadowing the
/// genuine family — whnf sticks at `Subtype.val` on large submodule-coercion
/// terms (`LieDerivation.ofGradingSum._proof_4`). Import lane drops the whole
/// seeded family (genuine imports); default lane keeps it.
#[test]
fn test_ws_level_import_prelude_suppresses_explicit_binder_subtype_family() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in ["Subtype", "Subtype.mk", "Subtype.val", "Subtype.property"] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}`"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed the explicit-binder `{c}`"
        );
    }
}

/// v4.30 census: Clean's rec-based `Ordering.isEq` spelling is NOT defeq to
/// Lean v4.30's wildcard-match compilation (`Ordering.then._sparseCasesOn_1`
/// with a higher-order continuation motive), so the seeded twin blocked the
/// genuine olean definition at the value-defeq dedup (Init.Data.Ord.Basic).
/// Import lane drops the seed (genuine imports through checked add_decl);
/// default lane keeps the rec spelling for proof execution.
#[test]
fn test_ws_ordering_iseq_suppressed_in_import_mode() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        default_env
            .get_const(&Name::from_string("Ordering.isEq"))
            .is_some(),
        "default lane keeps the Clean-native `Ordering.isEq`"
    );
    assert!(
        import_env
            .get_const(&Name::from_string("Ordering.isEq"))
            .is_none(),
        "import lane must NOT pre-seed the rec-based `Ordering.isEq` — it \
         blocks the genuine v4.30 sparse-casesOn definition at the dedup"
    );
}

/// v4.30 census (2026-07-06, Class 1): Clean seeds 14 `List.*` prelude
/// functions, the Clean-only `List.rangeAux` helper, and `Nat.shiftLeft` as
/// direct `List.rec`/`Nat.rec` eliminations — Lean v4.30 stores brecOn
/// towers (`Nat.shiftLeft` additionally recurses multiply-FIRST vs Clean's
/// multiply-LAST), so every seeded twin failed the value-defeq dedup
/// ("duplicate of seeded constant X: value not definitionally equal") and
/// the eq_def/lemma cascades followed (Init.Prelude, Init.Data.List.*,
/// Init.Data.Nat.Bitwise/Lemmas). Import lane drops the whole cluster plus
/// its seeded dependents (`List.reverse` — structurally faithful but built
/// on the gated `reverseAux`; the `List.append_nil`/`List.length_*` lemmas;
/// `instBEqList`; `instHAppendListList`; `instHShiftLeftNat`; `Array.size`)
/// so the genuine olean definitions import through the checked add_decl
/// path. Default lane keeps every seed.
#[test]
fn test_ws_list_recursion_cluster_suppressed_in_import_mode() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        // The 14 census List.* seeds + the Clean-only rangeAux helper.
        "List.append",
        "List.foldl",
        "List.length",
        "List.map",
        "List.set",
        "List.all",
        "List.any",
        "List.beq",
        "List.filter",
        "List.find?",
        "List.foldr",
        "List.range",
        "List.rangeAux",
        "List.replicate",
        "List.reverseAux",
        // Same-mechanism Nat seed (multiply-last vs brecOn multiply-first).
        "Nat.shiftLeft",
        // Dependent-init closure: seeds whose values/statements reference the
        // gated constants above.
        "List.reverse",
        "List.append_nil",
        "List.length_nil",
        "List.length_cons",
        "List.length_append",
        "instBEqList",
        "instHAppendListList",
        "instHShiftLeftNat",
        "Array.size",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed `{c}` — the direct-rec seed blocks \
             the genuine v4.30 brecOn definition at the value-defeq dedup"
        );
    }
    // The List substrate and the NON-divergent neighbours stay in both lanes:
    // `List.get?` and `List.tail` are Clean seeds with no census collision,
    // and the Option combinators ride `init_list_ops` (kept so import-mode
    // callers still get them). `Nat.shiftRight` stays as the upgradeable
    // VALUE-LESS axiom.
    for c in [
        "List",
        "List.nil",
        "List.cons",
        "List.rec",
        "List.get?",
        "List.tail",
        "Option.map",
        "Option.bind",
        "Option.getD",
        "Nat.shiftRight",
        "HShiftLeft",
        "Array",
        "Array.mk",
        "Array.data",
    ] {
        assert!(
            import_env.get_const(&Name::from_string(c)).is_some(),
            "`{c}` must remain available in the import prelude"
        );
    }
}

/// v4.30 census 2026-07-06 (pinpoint dcb769d4): Clean's Nat CORE ARITHMETIC
/// seeds diverge from Lean v4.30's genuine bodies — Lean stores brecOn towers
/// (add/mul/sub/pow/beq/ble), a structural arity-2 `Nat.modCore`, and
/// `@[irreducible]` WF div/mod, while Clean seeds direct `Nat.rec`
/// eliminations plus a fuel-peeling div/mod dispatcher. Two failure
/// mechanisms: (a) every seeded twin failed the import value-defeq dedup
/// ("duplicate of seeded constant Nat.add/…" — the 11 Init.Prelude census
/// rows), blocking the genuine defs and cascading the eq_def/lemma web;
/// (b) whnf digging into the seeded dispatcher unary-peeled 2^32-scale
/// literals (`Char.toUpper._proof_1`: 1,999,814 Nat.rec iota steps = the
/// whole 2M heartbeat budget — the 91-row heartbeat census class). The import
/// lane withholds the cluster + its dependent seeded web so the genuine olean
/// definitions register through the checked add_decl path; the name-keyed
/// native reducers still accelerate the imported constants. The default lane
/// keeps every member byte-identical.
#[test]
fn test_ws_nat_core_arith_cluster_suppressed_in_import_mode() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        // The 10 census core seeds.
        "Nat.add",
        "Nat.mul",
        "Nat.sub",
        "Nat.div",
        "Nat.mod",
        "Nat.pow",
        "Nat.modCore",
        "Nat.beq",
        "Nat.ble",
        "Nat.blt",
        // Clean-only fuel helper riding the gate (value references Nat.sub).
        "Nat.divCore",
        // Instance wrappers over the gated ops.
        "instHAddNat",
        "instHSubNat",
        "instHMulNat",
        "instHDivNat",
        "instHModNat",
        "instHPowNat",
        "instBEqNat",
        // Dependent seeded-lemma web (samples from each gated init):
        // init_nat_arith_lemmas
        "Nat.add_comm",
        "Nat.add_assoc",
        "Nat.zero_add",
        "Nat.mul_assoc",
        "Nat.left_distrib",
        // init_nat_sub_simp_lemmas
        "Nat.add_sub_cancel",
        "Nat.zero_sub",
        "Nat.sub_one",
        // init_nat_div_mod_lemmas (2 of the 11 census dup rows)
        "Nat.mod_lt",
        "Nat.divmodAux.modCore_lt",
        // algebra_nat_mul_cancel_proof web
        "Nat.zero_le",
        "Nat.le_add_right",
        "Nat.mul_le_mul_left",
        "Nat.le_or_lt",
        // nat_arith_order_proof web
        "Nat.add_le_add_left",
        "Nat.sub_le",
        // ble↔le bridge
        "Nat.ble_refl",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed `{c}` — the Clean-native Nat core \
             arithmetic seed blocks the genuine v4.30 definition at the \
             value-defeq dedup / unary-grinds huge literals"
        );
    }
    // The Nat substrate stays in both lanes: the inductive + ctors + rec, the
    // defeq-faithful `Nat.pred`, the `Nat.le`/`Nat.lt` order predicates, and
    // the heterogeneous op CLASSES (only the Nat instances are withheld).
    // `Nat.land`/`lor`/`xor`/`shiftRight`/`testBit` stay as upgradeable
    // VALUE-LESS axioms. (`Nat.compare` is not asserted either way: its only
    // import-prelude entry rode the gated `instBEqNat` init, so it is simply
    // absent — the genuine olean definition imports on demand.)
    for c in [
        "Nat",
        "Nat.zero",
        "Nat.succ",
        "Nat.rec",
        "Nat.pred",
        "Nat.le",
        "Nat.lt",
        "HAdd",
        "HSub",
        "HMul",
        "HDiv",
        "HMod",
        "HPow",
        "BEq",
        "Nat.land",
        "Nat.lor",
        "Nat.xor",
        "Nat.shiftRight",
        "Nat.testBit",
    ] {
        assert!(
            import_env.get_const(&Name::from_string(c)).is_some(),
            "`{c}` must remain available in the import prelude"
        );
    }
    for axiom in ["Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftRight"] {
        let info = import_env
            .get_const(&Name::from_string(axiom))
            .expect("checked present above");
        assert!(
            info.value.is_none(),
            "import-lane `{axiom}` must stay the upgradeable VALUE-LESS axiom"
        );
    }
}

/// v4.30 census: Clean's `OptionT.fail` stub is REDUCED-ARITY (`{m} → {α} →
/// OptionT m α`; genuine v4.30 adds `[inst : Monad m]` between them), so the
/// seeded axiom shadowed the genuine definition and masked
/// `OptionT.instAlternative` / `OptionT.instMonadExceptOfPUnit`
/// (Init.Control.Option). Import lane drops the stub (genuine imports with
/// its value); default lane keeps it for the do-notation lowering, which
/// cannot supply a Monad instance today.
#[test]
fn test_ws_option_t_fail_suppressed_in_import_mode() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        default_env
            .get_const(&Name::from_string("OptionT.fail"))
            .is_some(),
        "default lane keeps the reduced-arity `OptionT.fail` stub"
    );
    assert!(
        import_env
            .get_const(&Name::from_string("OptionT.fail"))
            .is_none(),
        "import lane must NOT pre-seed the reduced-arity `OptionT.fail` — it \
         shadows the genuine `[Monad m]`-binder definition"
    );
}

/// v4.30 closing census (2026-07-15) — ring 2 of the Nat core-arithmetic
/// suppression: Lean v4.30's Init.Data.Ord.Basic stores `instOrdNat :=
/// ⟨fun x y => compareOfLessAndEq x y⟩`, a match-compiled `instOrdBool`, and
/// `instOrdOrdering := ⟨compareOn (·.ctorIdx)⟩` — with NO named
/// `Nat.compare`/`Bool.compare`/`Ordering.compare` constants at all. Clean's
/// rec-spelled instance seeds blocked the genuine olean definitions at the
/// value-defeq dedup (Init.Data.Ord.Basic 3 dup rows), and the surviving
/// Clean spellings failed the genuine lemma re-checks stated over them
/// (Init.Data.Nat.Compare 10, Init.Data.Order.Ord 3,
/// Init.Grind.Ring.CommSolver 20). Import lane drops the cluster (genuine
/// instances import through checked add_decl); default lane keeps every seed.
#[test]
fn test_ws_ord_instance_cluster_suppressed_in_import_mode() {
    let default_env = Environment::try_with_prelude().expect("default prelude");
    let import_env = Environment::try_with_prelude_for_import().expect("import prelude");
    for c in [
        // The 3 census dup roots (Init.Data.Ord.Basic).
        "instOrdNat",
        "instOrdBool",
        "instOrdOrdering",
        // Their Clean-only compare-fn spellings (genuine v4.30 has no
        // constants under these names; the instance fields are anonymous
        // lambdas / matchers).
        "Nat.compare",
        "Bool.compare",
        "Ordering.compare",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "default lane keeps the Clean-native `{c}` (no proof-execution change)"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_none(),
            "import lane must NOT pre-seed `{c}` — the Clean-native Ord \
             instance cluster blocks the genuine v4.30 definition at the \
             value-defeq dedup / fails the genuine Nat.compare_* lemma web"
        );
    }
    // The import-faithful Ord substrate stays in both lanes: the class, its
    // projection, and the Ordering enum backbone.
    for c in [
        "Ord",
        "Ord.mk",
        "Ord.compare",
        "Ordering",
        "Ordering.lt",
        "Ordering.eq",
        "Ordering.gt",
        "Ordering.swap",
    ] {
        assert!(
            default_env.get_const(&Name::from_string(c)).is_some(),
            "`{c}` must remain available in the default prelude"
        );
        assert!(
            import_env.get_const(&Name::from_string(c)).is_some(),
            "`{c}` must remain available in the import prelude"
        );
    }
}
