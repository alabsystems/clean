// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR0 commit A: the fenced Lean-reference entry (`clean_kernel::reference`).
//!
//! Every refusal here has a control showing the same term is otherwise
//! well-formed (so the FENCE refused it, not some unrelated error), and the
//! positive controls show the fence does not refuse everything. The two
//! controls that need a native reducer Clean's native-fold authority now
//! closes in every theory (`isOSX` under `Extended`) live in
//! `crates/clean-olean/tests/reference_entry_fold_controls.rs`, because the
//! authority bypass they use is process-global and compiled only under
//! `clean-kernel/test-fixtures`, which `clean-olean`'s dev-dependency enables. The `String.drop` case needs the pinned Lean 4.30 `Init`
//! and lives in `crates/clean-olean/tests/reference_entry_string_drop.rs`.

use std::sync::Arc;

use clean_kernel::env::{KernelTheory, LeanTheoryExclusion};
use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::reference::theory_digest;
use clean_kernel::{
    BinderInfo, CleanMode, Constructor, Declaration, DeclarationVerification, EnvError,
    Environment, Expr, ExprKind, InductiveDecl, InductiveType, Level, MmAxiomOnlyGuard, Name,
    NonLeanKind, ReferenceKernel, ReferenceRefusal, TheoryId, TypeChecker,
};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn bool_ty() -> Expr {
    c("Bool")
}

/// `@Eq.{1} ty a b`.
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(name("Eq"), vec![Level::succ(Level::zero())]),
        [ty, a, b],
    )
}

/// `@Eq.refl.{1} ty a`.
fn refl(ty: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(name("Eq.refl"), vec![Level::succ(Level::zero())]),
        [ty, a],
    )
}

fn theorem(n: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: name(n),
        level_params: vec![],
        type_,
        value,
    }
}

fn def(n: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: name(n),
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
    }
}

fn entry() -> ReferenceKernel {
    ReferenceKernel::new(Environment::with_prelude()).expect("the prelude passes the base walk")
}

// ---------------------------------------------------------------------------
// 1. isOSX
// ---------------------------------------------------------------------------

/// The prelude plus Lean's two platform declarations, spelled as Lean's kernel
/// holds them (`Init/System/Platform.lean`): an OPAQUE extern and a
/// definition over it.
fn platform_env() -> Environment {
    let mut env = Environment::with_prelude();
    let unit = c("Unit");
    env.add_decl(Declaration::Opaque {
        name: name("System.Platform.getIsOSX"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, unit.clone(), bool_ty()),
        value: Expr::lam(BinderInfo::Default, unit, c("Bool.false")),
    })
    .expect("opaque getIsOSX is well-typed");
    env.add_decl(def(
        "System.Platform.isOSX",
        bool_ty(),
        Expr::app(c("System.Platform.getIsOSX"), c("Unit.unit")),
    ))
    .expect("def isOSX is well-typed");
    env
}

/// `isOSX = b := Eq.refl b`.
fn is_osx_is(b: bool) -> Declaration {
    let lit = c(if b { "Bool.true" } else { "Bool.false" });
    theorem(
        if b {
            "kr0_is_osx_true"
        } else {
            "kr0_is_osx_false"
        },
        eq(bool_ty(), c("System.Platform.isOSX"), lit.clone()),
        refl(bool_ty(), lit),
    )
}

/// Both spellings refuse through the entry, on every host, and the refusal
/// names the reducer family Lean's kernel does not have.
#[test]
fn test_is_osx_both_spellings_refused_through_the_entry() {
    let mut k = ReferenceKernel::new(platform_env()).expect("platform base passes the walk");
    for b in [true, false] {
        let err = k
            .add_checked(is_osx_is(b))
            .expect_err("Lean's kernel cannot reduce the opaque extern");
        assert!(
            matches!(
                err,
                ReferenceRefusal::TheoryExclusion(LeanTheoryExclusion::OpaqueExternFamily)
            ),
            "isOSX = {b}: expected TheoryExclusion(OpaqueExternFamily), got {err:?}"
        );
    }
    // Control: the stuck term is still well-formed; reflexivity on it checks.
    let is_osx = c("System.Platform.isOSX");
    k.add_checked(theorem(
        "kr0_is_osx_refl",
        eq(bool_ty(), is_osx.clone(), is_osx.clone()),
        refl(bool_ty(), is_osx),
    ))
    .expect("reflexivity on the stuck platform boolean is accepted");
}

// ---------------------------------------------------------------------------
// 3. The fourteen non-Lean expression forms
// ---------------------------------------------------------------------------

fn k(kind: ExprKind) -> Expr {
    Expr::from_kind(kind)
}

fn a(e: Expr) -> Arc<Expr> {
    Arc::new(e)
}

/// `∀ p : Prop, p` — a closed proposition (an element of `Prop`).
fn p() -> Expr {
    Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0))
}

fn interval() -> Expr {
    k(ExprKind::CubicalInterval)
}

/// `fun _ : I => Prop`, a constant line of types.
fn prop_line() -> Expr {
    Expr::lam(BinderInfo::Default, interval(), Expr::prop())
}

fn zfc_empty() -> Expr {
    k(ExprKind::ZFCSet(ZFCSetExpr::Empty))
}

/// One minimal term per non-Lean form, with the mode its own theory needs.
fn non_lean_terms() -> Vec<(NonLeanKind, CleanMode, Expr)> {
    use CleanMode::{Cubical, Impredicative, SetTheoretic};
    let i0 = || k(ExprKind::CubicalI0);
    let i1 = || k(ExprKind::CubicalI1);
    let path_lam = || k(ExprKind::CubicalPathLam { body: a(p()) });
    vec![
        (NonLeanKind::SProp, Impredicative, k(ExprKind::SProp)),
        (
            NonLeanKind::Squash,
            Impredicative,
            k(ExprKind::Squash(a(Expr::prop()))),
        ),
        (NonLeanKind::CubicalInterval, Cubical, interval()),
        (NonLeanKind::CubicalI0, Cubical, i0()),
        (NonLeanKind::CubicalI1, Cubical, i1()),
        (
            NonLeanKind::CubicalPath,
            Cubical,
            k(ExprKind::CubicalPath {
                ty: a(prop_line()),
                left: a(p()),
                right: a(p()),
            }),
        ),
        (NonLeanKind::CubicalPathLam, Cubical, path_lam()),
        (
            NonLeanKind::CubicalPathApp,
            Cubical,
            k(ExprKind::CubicalPathApp {
                path: a(path_lam()),
                arg: a(i0()),
            }),
        ),
        (
            NonLeanKind::CubicalHComp,
            Cubical,
            k(ExprKind::CubicalHComp {
                ty: a(Expr::prop()),
                phi: a(i0()),
                u: a(Expr::lam(BinderInfo::Default, interval(), p())),
                base: a(p()),
            }),
        ),
        (
            NonLeanKind::CubicalTransp,
            Cubical,
            k(ExprKind::CubicalTransp {
                ty: a(prop_line()),
                phi: a(i0()),
                base: a(p()),
            }),
        ),
        (
            NonLeanKind::CubicalCoe,
            Cubical,
            k(ExprKind::CubicalCoe {
                ty: a(prop_line()),
                r: a(i0()),
                s: a(i1()),
                base: a(p()),
            }),
        ),
        (NonLeanKind::ZFCSet, SetTheoretic, zfc_empty()),
        (
            NonLeanKind::ZFCMem,
            SetTheoretic,
            k(ExprKind::ZFCMem {
                element: a(zfc_empty()),
                set: a(zfc_empty()),
            }),
        ),
        (
            NonLeanKind::ZFCComprehension,
            SetTheoretic,
            k(ExprKind::ZFCComprehension {
                domain: a(zfc_empty()),
                pred: a(Expr::lam(BinderInfo::Default, c("ZFC.Set"), p())),
            }),
        ),
    ]
}

/// An environment in `mode` under `Extended`, with the one constant the ZFC
/// forms are typed by.
fn mode_env(mode: CleanMode) -> Environment {
    let mut env = Environment::with_mode(mode);
    if mode == CleanMode::SetTheoretic {
        env.add_decl(Declaration::Axiom {
            name: name("ZFC.Set"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .expect("ZFC.Set : Type");
    }
    env
}

/// The term as a definition at the type the kernel itself infers for it in
/// its own mode, under `Extended` (the control's half of the pair).
fn as_checked_definition(kind: NonLeanKind, mode: CleanMode, term: &Expr) -> Declaration {
    let env = mode_env(mode);
    assert_eq!(env.kernel_theory(), KernelTheory::Extended);
    let ty = TypeChecker::new(&env)
        .infer_type(term)
        .unwrap_or_else(|e| panic!("{kind:?}: the term infers in {mode:?}: {e:?}"));
    let d = def(&format!("kr0_{kind:?}"), ty, term.clone());
    env.check_decl_readonly(&d)
        .unwrap_or_else(|e| panic!("{kind:?}: control, accepted in {mode:?}: {e:?}"));
    d
}

#[test]
fn test_each_non_lean_kind_refused_with_its_own_kind() {
    let terms = non_lean_terms();
    assert_eq!(terms.len(), 14, "one term per NonLeanKind");
    for (kind, mode, term) in terms {
        // Control: the term is a well-typed definition in its own theory.
        let d = as_checked_definition(kind, mode, &term);
        // The fence: the same declaration through the entry.
        let mut entry = ReferenceKernel::new(mode_env(CleanMode::Constructive))
            .expect("an empty Constructive base passes the walk");
        let err = entry
            .add_checked(d.clone())
            .expect_err("the fence refuses it");
        assert!(
            matches!(err, ReferenceRefusal::NonLeanExprKind { kind: got, .. } if got == kind),
            "{kind:?}: expected NonLeanExprKind {{ kind: {kind:?} }}, got {err:?}"
        );
        // And in check_closed_term.
        let (ty, val) = match &d {
            Declaration::Definition { type_, value, .. } => (type_.clone(), value.clone()),
            _ => unreachable!(),
        };
        let err = entry
            .check_closed_term(&ty, &val)
            .expect_err("the fence refuses the closed term too");
        assert!(
            matches!(err, ReferenceRefusal::NonLeanExprKind { kind: got, .. } if got == kind),
            "{kind:?}: closed term, got {err:?}"
        );
    }
}

/// A non-Lean form anywhere in the BASE refuses `new`, and names the kind.
#[test]
fn test_each_non_lean_kind_in_the_base_refuses_new() {
    for (kind, mode, term) in non_lean_terms() {
        let d = as_checked_definition(kind, mode, &term);
        let mut base = mode_env(mode);
        base.add_decl(d).expect("control: the base accepts it");
        let err = ReferenceKernel::new(base).expect_err("the base walk refuses it");
        assert!(
            matches!(&err, ReferenceRefusal::NonLeanExprKind { kind: got, decl }
                if *got == kind && decl.to_string() == format!("kr0_{kind:?}")),
            "{kind:?}: got {err:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// 4. A citation laundered through the base
// ---------------------------------------------------------------------------

/// `(fun _ : ZFC.Set => Prop) (ZFCSet ∅)`, a type (it reduces to `Prop`)
/// whose spelling uses `ZFCSet`.
fn zfc_laundered_type() -> Expr {
    Expr::app(
        Expr::lam(BinderInfo::Default, c("ZFC.Set"), Expr::prop()),
        zfc_empty(),
    )
}

#[test]
fn test_base_constant_whose_type_uses_zfc_set_refuses_new() {
    let mut base = mode_env(CleanMode::SetTheoretic);
    base.add_decl(Declaration::Axiom {
        name: name("kr0_bad"),
        level_params: vec![],
        type_: zfc_laundered_type(),
    })
    .expect("control: the set-theoretic base accepts the axiom");
    let err = ReferenceKernel::new(base).expect_err("the base walk refuses it");
    assert!(
        matches!(&err, ReferenceRefusal::NonLeanExprKind { decl, kind: NonLeanKind::ZFCSet }
            if decl.to_string() == "kr0_bad"),
        "got {err:?}"
    );
    // Control: the same base without the axiom passes.
    ReferenceKernel::new(mode_env(CleanMode::SetTheoretic))
        .expect("control: the base without the axiom passes");
}

/// A clean base, then the bad constant through the entry: the walk refuses
/// it (the exact `ZFCSet` refusal, not a kernel error), and it never enters.
/// "A clean base that later holds a bad constant" cannot be built from
/// outside: `add_checked` is the only way in and it walks. So the citation
/// below refuses only as the kernel's unknown constant; the citation-time
/// walk itself is the unit test
/// `reference::tests::test_citation_of_an_unwalked_constant_is_checked_at_citation`.
/// Control: the same citation shape of a clean constant is accepted.
#[test]
fn test_refused_constant_never_enters_the_entry() {
    let mut k = entry();
    let err = k
        .add_checked(Declaration::Axiom {
            name: name("kr0_bad"),
            level_params: vec![],
            type_: zfc_laundered_type(),
        })
        .expect_err("the walk refuses the bad axiom");
    assert!(
        matches!(
            err,
            ReferenceRefusal::NonLeanExprKind {
                kind: NonLeanKind::ZFCSet,
                ..
            }
        ),
        "got {err:?}"
    );
    assert!(k.environment().get_const(&name("kr0_bad")).is_none());
    let citer = |cited: &str| {
        def(
            "kr0_citer",
            Expr::prop(),
            Expr::pi(BinderInfo::Default, c(cited), p()),
        )
    };
    let err = k
        .add_checked(citer("kr0_bad"))
        .expect_err("a citation of a constant that never entered refuses");
    assert!(matches!(err, ReferenceRefusal::Kernel(_)), "got {err:?}");

    // Control (a definition: since R143 an axiom outside Ax0 is refused by
    // the entry's own rule, `reference_ax0.rs`).
    k.add_checked(def(
        "kr0_good",
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
    ))
    .expect("a Lean definition is accepted");
    k.add_checked(citer("kr0_good"))
        .expect("the same citation of a clean constant is accepted");
}

// ---------------------------------------------------------------------------
// 5. Structural provenance and the Metamath two-pass
// ---------------------------------------------------------------------------

fn nat_zero_def(n: &str) -> Declaration {
    def(n, c("Nat"), Expr::nat_lit(0))
}

#[test]
fn test_structural_base_constant_refuses_new() {
    let mut base = Environment::with_prelude();
    base.add_decl_structural(nat_zero_def("kr0_structural"))
        .expect("structurally well-formed");
    assert_eq!(
        base.declaration_verification(&name("kr0_structural")),
        Some(DeclarationVerification::StructuralOnly)
    );
    let err = ReferenceKernel::new(base).expect_err("structural provenance refuses");
    assert!(
        matches!(&err, ReferenceRefusal::StructuralProvenance { decl } if decl.to_string() == "kr0_structural"),
        "got {err:?}"
    );
    // Control: the same declaration through the CHECKED path passes the walk.
    let mut base = Environment::with_prelude();
    base.add_decl(nat_zero_def("kr0_structural"))
        .expect("checked add");
    ReferenceKernel::new(base).expect("a checked constant passes");
}

#[test]
fn test_add_checked_refuses_inside_a_two_pass_scope() {
    let mut k = entry();
    {
        let _guard = MmAxiomOnlyGuard::enter();
        let err = k
            .add_checked(nat_zero_def("kr0_mm"))
            .expect_err("refused while the two-pass scope is live");
        assert!(
            matches!(err, ReferenceRefusal::MmTwoPassActive),
            "got {err:?}"
        );
        assert!(k.environment().get_const(&name("kr0_mm")).is_none());
    }
    // Control: once the guard drops, the same declaration is accepted.
    k.add_checked(nat_zero_def("kr0_mm"))
        .expect("accepted once the guard is gone");
}

// ---------------------------------------------------------------------------
// 5b. Checker settings
// ---------------------------------------------------------------------------

/// `def kr0_cum : Sort 2 := Nat`: well-typed only with cumulative subtyping
/// (`Nat : Sort 1 ≤ Sort 2`), which Lean's kernel does not have.
fn cumulative_only() -> Declaration {
    def(
        "kr0_cum",
        Expr::sort(Level::succ(Level::succ(Level::zero()))),
        nat(),
    )
}

/// A base with cumulative subtyping on, or ever on, refuses `new`. Controls:
/// the cumulative base really does accept the Lean-rejected declaration, and
/// the entry over a non-cumulative base refuses it.
#[test]
fn test_cumulative_base_refuses_new() {
    let mut base = Environment::with_prelude();
    base.set_cumulative(true);
    base.check_decl_readonly_strict(&cumulative_only())
        .expect("control: cumulative subtyping admits Sort 1 <= Sort 2");
    let err = ReferenceKernel::new(base.clone()).expect_err("a cumulative base refuses");
    assert!(
        matches!(
            err,
            ReferenceRefusal::NonLeanSetting {
                setting: "cumulative"
            }
        ),
        "got {err:?}"
    );
    // Turning it back off does not launder what was admitted meanwhile.
    base.add_decl(cumulative_only())
        .expect("admitted under cumulativity");
    base.set_cumulative(false);
    let err = ReferenceKernel::new(base).expect_err("a once-cumulative base refuses");
    assert!(
        matches!(
            err,
            ReferenceRefusal::NonLeanSetting {
                setting: "cumulative"
            }
        ),
        "got {err:?}"
    );
    // Control: through the entry the declaration is Lean's refusal.
    let mut k = entry();
    let err = k
        .add_checked(cumulative_only())
        .expect_err("Lean's kernel has no cumulativity");
    assert!(matches!(err, ReferenceRefusal::Kernel(_)), "got {err:?}");
    assert!(!k.environment().checker_settings().cumulative);
}

/// Whatever theory and mode the base had, every checker the entry builds
/// reads Lean's: the snapshot the checking paths read says so.
#[test]
fn test_entry_checker_settings_are_leans() {
    let mut base = Environment::with_prelude();
    base.set_kernel_theory(KernelTheory::Extended);
    assert_eq!(base.checker_settings().mode, CleanMode::Classical);
    let k = ReferenceKernel::new(base).expect("the prelude passes");
    let s = k.environment().checker_settings();
    assert_eq!(s.kernel_theory, KernelTheory::LeanReference);
    assert_eq!(s.mode, CleanMode::Constructive);
    assert!(!s.cumulative && !s.cumulative_ever);
}

// ---------------------------------------------------------------------------
// 6. Positive controls
// ---------------------------------------------------------------------------

fn nat() -> Expr {
    c("Nat")
}

#[test]
fn test_nat_literal_arithmetic_is_accepted() {
    let mut k = entry();
    let two = Expr::nat_lit(2);
    let lhs = Expr::apps(c("Nat.add"), [two.clone(), two]);
    let before = k.env_digest();
    let token = k
        .add_checked(theorem(
            "kr0_two_add_two",
            eq(nat(), lhs, Expr::nat_lit(4)),
            refl(nat(), Expr::nat_lit(4)),
        ))
        .expect("2 + 2 = 4 by rfl, through Lean's own Nat extension");
    assert_eq!(token.theory_id(), TheoryId::LeanReferenceV1);
    assert_eq!(token.env_digest(), k.env_digest());
    assert_ne!(
        before,
        k.env_digest(),
        "an admitted declaration moves the digest"
    );
    // Control: a false equation is refused.
    let lhs = Expr::apps(c("Nat.add"), [Expr::nat_lit(2), Expr::nat_lit(2)]);
    let err = k
        .add_checked(theorem(
            "kr0_two_add_two_five",
            eq(nat(), lhs, Expr::nat_lit(5)),
            refl(nat(), Expr::nat_lit(5)),
        ))
        .expect_err("2 + 2 = 5 is refused");
    assert!(matches!(err, ReferenceRefusal::Kernel(_)), "got {err:?}");
}

#[test]
fn test_string_literal_rfl_is_accepted() {
    let k = entry();
    let s = Expr::str_lit("abc");
    let token = k
        .check_closed_term(
            &eq(c("String"), s.clone(), s.clone()),
            &refl(c("String"), s),
        )
        .expect("\"abc\" = \"abc\" by rfl");
    assert_eq!(token.theory_id(), TheoryId::LeanReferenceV1);
    // Control: two different literals are refused.
    let err = k
        .check_closed_term(
            &eq(c("String"), Expr::str_lit("abc"), Expr::str_lit("abd")),
            &refl(c("String"), Expr::str_lit("abd")),
        )
        .expect_err("\"abc\" = \"abd\" is refused");
    assert!(matches!(err, ReferenceRefusal::Kernel(_)), "got {err:?}");
}

/// A two-constructor inductive in the base (its kernel-generated eliminators
/// pass the provenance walk), and a definition computing by ι over it.
#[test]
fn test_small_inductive_is_accepted() {
    let two = name("KR0Two");
    let mut base = Environment::with_prelude();
    base.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: two.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: two.clone().str("a"),
                    type_: c("KR0Two"),
                },
                Constructor {
                    name: two.clone().str("b"),
                    type_: c("KR0Two"),
                },
            ],
        }],
    })
    .expect("a two-constructor inductive");
    // The family's generated eliminators earned the full stamp (the base walk
    // has no exception for them).
    for member in ["KR0Two", "KR0Two.a", "KR0Two.rec", "KR0Two.casesOn"] {
        assert_eq!(
            base.declaration_verification(&name(member)),
            Some(DeclarationVerification::FullKernelCheck),
            "{member}"
        );
    }
    let mut k = ReferenceKernel::new(base).expect("the family passes the walk");
    // flip := fun x => KR0Two.rec.{1} (motive := fun _ => KR0Two) b a x
    let motive = Expr::lam(BinderInfo::Default, c("KR0Two"), c("KR0Two"));
    let flip_body = Expr::apps(
        Expr::const_(name("KR0Two.rec"), vec![Level::succ(Level::zero())]),
        [motive, c("KR0Two.b"), c("KR0Two.a"), Expr::bvar(0)],
    );
    k.add_checked(def(
        "KR0Two.flip",
        Expr::arrow(c("KR0Two"), c("KR0Two")),
        Expr::lam(BinderInfo::Default, c("KR0Two"), flip_body),
    ))
    .expect("a definition by the recursor");
    let flip_a = Expr::app(c("KR0Two.flip"), c("KR0Two.a"));
    k.add_checked(theorem(
        "KR0Two.flip_a",
        eq(c("KR0Two"), flip_a.clone(), c("KR0Two.b")),
        refl(c("KR0Two"), c("KR0Two.b")),
    ))
    .expect("flip a = b by ι");
    // Control: flip a = a is refused.
    let err = k
        .add_checked(theorem(
            "KR0Two.flip_a_bad",
            eq(c("KR0Two"), flip_a, c("KR0Two.a")),
            refl(c("KR0Two"), c("KR0Two.a")),
        ))
        .expect_err("flip a = a is refused");
    assert!(matches!(err, ReferenceRefusal::Kernel(_)), "got {err:?}");
}

/// Equal bases give equal environment digests; the digest is not the theory.
#[test]
fn test_env_digest_is_deterministic_and_separate_from_the_theory() {
    let a = entry();
    let b = entry();
    assert_eq!(a.env_digest(), b.env_digest());
    assert_ne!(a.env_digest().0, a.theory_id().digest());
    let c = ReferenceKernel::new(platform_env()).expect("platform base");
    assert_ne!(
        a.env_digest(),
        c.env_digest(),
        "a different base, a different digest"
    );
    assert_eq!(a.environment().kernel_theory(), KernelTheory::LeanReference);
    assert_eq!(a.environment().mode(), CleanMode::Constructive);
}

// ---------------------------------------------------------------------------
// 7. The theory-id pin
// ---------------------------------------------------------------------------

const LEAN_REFERENCE_V1_HEX: &str =
    "3a3b95be372096ca4bac5cbcb35f789775408f94c19670257a57188d71b53591";

fn hex(d: [u8; 32]) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn test_theory_id_digest_is_pinned_and_moves_with_its_inputs() {
    let id = TheoryId::LeanReferenceV1;
    assert_eq!(id.nat_extensions().len(), 14);
    assert_eq!(id.tags(), ["string-literal-expansion"]);
    let live = theory_digest(id.nat_extensions(), id.tags());
    assert_eq!(live, id.digest());
    assert_eq!(hex(id.digest()), LEAN_REFERENCE_V1_HEX);

    let mut dropped: Vec<&str> = id.nat_extensions().to_vec();
    dropped.retain(|h| *h != "Nat.gcd");
    let mut added: Vec<&str> = id.nat_extensions().to_vec();
    added.push("Nat.log2");
    let mut swapped: Vec<&str> = id.nat_extensions().to_vec();
    swapped.swap(0, 1);
    for (label, nat, tags) in [
        ("dropped Nat.gcd", dropped, id.tags().to_vec()),
        ("added Nat.log2", added, id.tags().to_vec()),
        ("swapped order", swapped, id.tags().to_vec()),
        ("no string tag", id.nat_extensions().to_vec(), vec![]),
    ] {
        assert_ne!(theory_digest(&nat, &tags), id.digest(), "{label}");
    }
    assert_eq!(id.kernel_theory(), KernelTheory::LeanReference);
    assert_eq!(id.mode(), CleanMode::Constructive);
    let json = serde_json::to_string(&id).expect("serialize");
    assert_eq!(
        serde_json::from_str::<TheoryId>(&json).expect("round trip"),
        id
    );
}

/// The kernel's refusal is passed through unchanged when no excluded reducer
/// is involved (here: a theorem whose type is not a proposition).
#[test]
fn test_other_kernel_refusals_pass_through() {
    let mut k = entry();
    let err = k
        .add_checked(theorem("kr0_not_prop", nat(), Expr::nat_lit(0)))
        .expect_err("a theorem must be a proof");
    assert!(
        matches!(
            err,
            ReferenceRefusal::Kernel(EnvError::TheoremTypeNotProp { .. })
        ),
        "got {err:?}"
    );
}
