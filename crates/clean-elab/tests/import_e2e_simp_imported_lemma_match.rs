// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: does `simp only [f.eq_def]` MATCH and FIRE an imported equation
//! lemma at a *use* of a reducible imported function? (simp_imported_lemma_match)
//!
//! ## The B53 sibling question
//!
//! B53 (`import_e2e_imported_wf_definition`, commit 69808d4) fixed env-constant
//! `rw`: `Unifier::unify` WHNF-reduces BOTH sides before structural comparison,
//! so rewriting a *use* of a *reducible* defined function (e.g. an imported WF
//! def that iota-reduces on a constructor-headed `Acc.intro`) reduced the term
//! to its value before the pattern `f ?x` could bind — a spurious
//! `RewriteNoMatch`. B53 added a keyed head-symbol pre-match to `rw` but
//! EXPLICITLY left simp's matcher unchanged ("broader blast radius"), noting only
//! that for a *reducible* use `simp only` *closes by def-eq* (so firing vs not
//! is unobservable there). This probe answers the open question: does simp's
//! lemma matcher have the SAME defect on a use it cannot close by def-eq?
//!
//! ## Why the reducible case can't decide it — and the shape that can
//!
//! For the reducible `fInline` (its accessibility witness is an *inlined*
//! `Acc.intro`, so `fInline n` iota-reduces to `Nat.add n n`), the use-site is
//! definitionally equal to the equation's RHS, so `simp only [fInline.eq_def]`
//! soundly closes `fInline 4 = g 4` by `rfl` **whether or not the named lemma
//! fires** — the lemma is redundant and firing is unobservable (Probe R, locked
//! in below: `closed = true`, `fired = false`).
//!
//! The decisive shape is the GENUINELY STUCK one — and it is also the *realistic*
//! `.olean` WF-def shape. A Lean-compiled WF function bottoms out in an OPAQUE /
//! irreducible accessibility witness, so `fStuck n` does NOT iota-reduce (`whnf`
//! will not unfold an `Opaque` constant; the major premise of `Acc.rec` never
//! becomes `Acc.intro`). Then `fStuck 4` is NOT definitionally equal to `g 4`
//! (asserted below), so the *only* way to close `fStuck 4 = g 4` is to actually
//! FIRE the equation lemma. Firing is fully observable: the closing proof
//! references `fStuck.eq_def`, and the no-lemma control cannot close at all.
//!
//! ## Finding (validation, no bug)
//!
//! On the genuinely-stuck use, **simp's matcher fires the imported equation
//! lemma correctly** (Probe S): `simp only [fStuck.eq_def]` closes
//! `fStuck 4 = g 4` with a kernel-checked, sorry-free, axiom-free proof that
//! references the lemma. simp does NOT exhibit the B53 `rw` defect on the
//! realistic shape, because the stuck use never WHNF-reduces — its head stays
//! `Acc.rec`/`fStuck`, so both the discrimination-tree index slot (built from
//! the lemma's stuck LHS `fStuck ?x`) and the use-site query key on the same
//! head, and `Unifier::unify(fStuck ?x, fStuck 4)` matches rigidly without
//! reducing either side away. The reducible `fInline` "non-firing" is not a bug:
//! a reducible use IS def-eq to the RHS, so simp's def-eq closer is sound and the
//! named lemma is redundant. (`rw`, by contrast, is a *targeted syntactic*
//! rewrite that must fire to make progress — hence the B53 keyed-match fix there
//! but not here.) No clean-elab change is warranted; this fixture LOCKS IN the
//! correct simp behavior as a regression guard.
//!
//! ## The imported (`.olean`) shape we reproduce
//!
//! Mirrors B53's `import_e2e_imported_wf_definition` recipe exactly: the kernel
//! builds `Acc` + `Acc.intro` + `Acc.rec` in a scratch env; we copy the
//! inductive / constructor / **registered recursor** verbatim into a fresh env
//! with **no** `init_well_founded` bootstrap, then build the WF defs *through the
//! clean-elab elaborator* over the imported `Acc.rec`. The reducible equation
//! lemma `fInline.eq_def` is a kernel-checked `Declaration::Theorem` (its `rfl`
//! proof checks because `fInline x` reduces to `g x`); the stuck equation lemma
//! `fStuck.eq_def` is a true-but-not-`rfl`-provable proposition (it needs
//! `WellFounded.fix_eq`, out of scope) registered structurally to emulate a
//! Lean-compiled equation lemma (see `register_stuck_eq_def_structural`).

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::env::{Declaration, DeclarationTrustSummary, Environment};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, RecursorArgOrder, TypeChecker};

use clean_elab::tactic::{simp, ProofState, SimpConfig};
use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers (mirror import_e2e_imported_wf_definition's Acc-import scaffolding)
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat() -> Expr {
    const_("Nat")
}

/// `Nat` literal `n` in the kernel's native literal representation.
fn nat_lit(n: u32) -> Expr {
    Expr::nat_lit(u64::from(n))
}

/// `Sort 1` — the universe `Nat : Type 0 = Sort 1` lives in.
fn lvl1() -> Level {
    Level::succ(Level::zero())
}

/// `Acc.{1}` — `Acc` specialised to a `Type`-level `α` (here `Nat`).
fn acc_c() -> Expr {
    Expr::const_(Name::from_string("Acc"), vec![lvl1()])
}

/// `@Eq Nat lhs rhs` (`Nat : Type`, so the `Eq` universe level is `1`).
fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![lvl1()]);
    Expr::app(Expr::app(Expr::app(eq, nat()), lhs), rhs)
}

/// `@f.{0…} arg` for a (possibly universe-polymorphic) elaborated function `f`,
/// instantiating each of its level params at `0`.
fn app_fn_at_zero(env: &Environment, f_name: &str, arg: Expr) -> Expr {
    let n = env
        .get_const(&Name::from_string(f_name))
        .map_or(0, |i| i.level_params.len());
    let levels = vec![Level::zero(); n];
    Expr::app(Expr::const_(Name::from_string(f_name), levels), arg)
}

/// Kernel-check an assembled closed `proof` against `goal_ty` via the trusted
/// `TypeChecker` — the authoritative acceptance check.
fn kernel_check_proof(env: &Environment, goal_ty: &Expr, proof: &Expr) {
    let tc = TypeChecker::new(env);
    tc.check_type(proof, goal_ty)
        .unwrap_or_else(|e| panic!("assembled proof must kernel-check against the goal: {e:?}"));
}

/// Reduce `expr` to whnf and return its head `Const` name / literal repr.
fn whnf_head(env: &Environment, expr: &Expr) -> String {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Lit(_) => format!("{:?}", reduced.kind()),
        _ => match reduced.get_app_fn().kind() {
            ExprKind::Const(n, _) => n.to_string(),
            other => format!("{other:?}"),
        },
    }
}

/// Build the `Acc` inductive with `Acc.intro`, mirroring Clean's
/// `init_well_founded` so the kernel-generated `Acc.rec` is byte-identical to an
/// `.olean`'s.
fn acc_decl() -> InductiveDecl {
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let sort_u = Expr::sort(u_level.clone());
    let prop = Expr::prop();
    let acc_const = Expr::const_(Name::from_string("Acc"), vec![u_level.clone()]);

    let mk_r_type = |alpha_depth: u32| -> Expr {
        let inner = Expr::pi(
            BinderInfo::Default,
            Expr::bvar(alpha_depth + 1),
            prop.clone(),
        );
        Expr::pi(BinderInfo::Default, Expr::bvar(alpha_depth), inner)
    };

    let acc_type = {
        let r_type = mk_r_type(0);
        let body = Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone());
        let body = Expr::pi(BinderInfo::Default, r_type, body);
        Expr::pi(BinderInfo::Implicit, sort_u.clone(), body)
    };

    let acc_ctor_type = {
        let r_y_x = Expr::app(Expr::app(Expr::bvar(2), Expr::bvar(0)), Expr::bvar(1));
        let acc_r_y = Expr::app(
            Expr::app(Expr::app(acc_const.clone(), Expr::bvar(4)), Expr::bvar(3)),
            Expr::bvar(1),
        );
        let imp = Expr::pi(BinderInfo::Default, r_y_x, acc_r_y);
        let h_type = Expr::pi(BinderInfo::Default, Expr::bvar(2), imp);
        let result = Expr::app(
            Expr::app(Expr::app(acc_const.clone(), Expr::bvar(3)), Expr::bvar(2)),
            Expr::bvar(1),
        );
        let body = Expr::pi(BinderInfo::Default, h_type, result);
        let body = Expr::pi(BinderInfo::Default, Expr::bvar(1), body);
        let r_type = mk_r_type(0);
        let body = Expr::pi(BinderInfo::Default, r_type, body);
        Expr::pi(BinderInfo::Implicit, sort_u, body)
    };

    InductiveDecl {
        level_params: vec![u],
        num_params: 2,
        types: vec![InductiveType {
            name: Name::from_string("Acc"),
            type_: acc_type,
            constructors: vec![Constructor {
                name: Name::from_string("Acc.intro"),
                type_: acc_ctor_type,
            }],
        }],
    }
}

/// A faithfully *imported* `Acc`: kernel-built family + constructor + `Acc.rec`
/// recursor copied verbatim into a fresh env, with **no** `init_well_founded`
/// bootstrap. `Acc.rec` is a registered recursor; `WellFounded.*` are absent.
fn imported_acc_env() -> Environment {
    let mut native = Environment::new();
    native.init_nat().expect("init_nat");
    native.init_true_false().expect("init_true_false");
    native.init_eq().expect("init_eq");
    native
        .add_inductive(acc_decl())
        .expect("Acc should declare");

    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env.init_eq().expect("init_eq");

    let iv = native
        .get_inductive(&Name::from_string("Acc"))
        .cloned()
        .expect("scratch env has Acc");
    env.register_inductive(iv);
    let ctor = native
        .get_constructor(&Name::from_string("Acc.intro"))
        .cloned()
        .expect("Acc.intro constructor");
    env.register_constructor(ctor);
    let rec_const = native
        .get_const(&Name::from_string("Acc.rec"))
        .cloned()
        .expect("Acc.rec const");
    env.extend_constants_unchecked(std::iter::once(rec_const));
    let rec_val = native
        .get_recursor(&Name::from_string("Acc.rec"))
        .cloned()
        .expect("Acc.rec recursor");
    env.register_recursor(rec_val);
    env
}

fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

/// Shared source: `g x := Nat.add x x` (the equation RHS) and the *reducible*
/// `fInline` (inlined `Acc.intro`, so `fInline n` iota-reduces to `Nat.add n n`).
const WF_DEFS: &str = "\
def emptyRel (a b : Nat) : Prop := False\n\
def g (x : Nat) : Nat := Nat.add x x\n\
def fInline (x : Nat) : Nat :=\n  \
  @Acc.rec Nat emptyRel (fun a _ => Nat) (fun y h ih => Nat.add y y) x\n    \
    (@Acc.intro Nat emptyRel x (fun (z : Nat) (hz : emptyRel z x) => False.elim hz))\n";

/// Register `fInline.eq_def : ∀ x, fInline x = g x` as a kernel `Theorem`
/// (proof `fun x => Eq.refl (g x)`; kernel-checks because `fInline x` reduces to
/// `g x`). A genuine, sorry-free, axiom-free imported equation lemma.
fn register_inline_eq_def(env: &mut Environment) {
    let level_params = env
        .get_const(&Name::from_string("fInline"))
        .map(|i| i.level_params.clone())
        .expect("fInline should be registered");
    let f_levels: Vec<Level> = level_params
        .iter()
        .map(|n| Level::param(n.clone()))
        .collect();
    let f_inline = Expr::const_(Name::from_string("fInline"), f_levels);

    let lhs = Expr::app(f_inline, Expr::bvar(0));
    let rhs = Expr::app(const_("g"), Expr::bvar(0));
    let ty = Expr::pi(BinderInfo::Default, nat(), nat_eq(lhs, rhs));

    let refl = Expr::const_(Name::from_string("Eq.refl"), vec![lvl1()]);
    let g_x = Expr::app(const_("g"), Expr::bvar(0));
    let refl_body = Expr::app(Expr::app(refl, nat()), g_x);
    let value = Expr::lam(BinderInfo::Default, nat(), refl_body);

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("fInline.eq_def"),
        level_params,
        type_: ty,
        value,
    })
    .expect("imported WF equation lemma fInline.eq_def should kernel-check and register");
}

/// Build the genuinely *non-reducing* WF def `fStuck` (the faithful `.olean`
/// shape): its accessibility witness is an **`Opaque`** constant
/// `accOpaque : ∀ x, Acc emptyRel x`, which `whnf` will not unfold, so
/// `@Acc.rec … (accOpaque x)` is STUCK — the major never becomes `Acc.intro`.
fn register_stuck_wf_def(env: &mut Environment) -> bool {
    let acc_at = |x: Expr| -> Expr {
        Expr::app(Expr::app(Expr::app(acc_c(), nat()), const_("emptyRel")), x)
    };
    let opaque_ty = Expr::pi(BinderInfo::Default, nat(), acc_at(Expr::bvar(0)));

    let intro = Expr::const_(Name::from_string("Acc.intro"), vec![lvl1()]);
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![lvl1()]);
    let acc_field = {
        let acc_r_z = Expr::app(
            Expr::app(Expr::app(acc_c(), nat()), const_("emptyRel")),
            Expr::bvar(1),
        );
        let body = Expr::app(Expr::app(false_elim, acc_r_z), Expr::bvar(0));
        let rel_z_x = Expr::app(Expr::app(const_("emptyRel"), Expr::bvar(0)), Expr::bvar(1));
        let inner = Expr::lam(BinderInfo::Default, rel_z_x, body);
        Expr::lam(BinderInfo::Default, nat(), inner)
    };
    let intro_app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(intro, nat()), const_("emptyRel")),
            Expr::bvar(0),
        ),
        acc_field,
    );
    let opaque_val = Expr::lam(BinderInfo::Default, nat(), intro_app);

    if env
        .add_decl(Declaration::Opaque {
            name: Name::from_string("accOpaque"),
            level_params: vec![],
            type_: opaque_ty,
            value: opaque_val,
        })
        .is_err()
    {
        return false;
    }

    elaborate_decls_into(
        env,
        "def fStuck (x : Nat) : Nat :=\n  \
         @Acc.rec Nat emptyRel (fun a _ => Nat) (fun y h ih => Nat.add y y) x (accOpaque x)\n",
    );
    true
}

/// Register `fStuck.eq_def : ∀ x, fStuck x = g x`.
///
// SOUNDNESS: test fixture only. `fStuck.eq_def : ∀ x, fStuck x = g x` is a true
// proposition — `accOpaque x` is proof-irrelevant-equal to the inlined
// `Acc.intro`, so `fStuck x` and `fInline x` denote the same value `g x` — but
// it cannot be checked by reduction because the `Opaque` witness blocks iota
// (this is exactly why Lean proves it via `WellFounded.fix_eq`). It is added
// structurally to emulate a Lean-compiled `.olean` equation lemma; no production
// code path uses `add_decl_structural`, and the proof a tactic builds *from* this
// lemma is kernel-checked against the goal type independently (`kernel_check_proof`).
// No new axiom is introduced into any production env.
fn register_stuck_eq_def_structural(env: &mut Environment) -> bool {
    let level_params = env
        .get_const(&Name::from_string("fStuck"))
        .map(|i| i.level_params.clone())
        .unwrap_or_default();
    let f_levels: Vec<Level> = level_params
        .iter()
        .map(|n| Level::param(n.clone()))
        .collect();
    let f_stuck = Expr::const_(Name::from_string("fStuck"), f_levels);

    let lhs = Expr::app(f_stuck, Expr::bvar(0));
    let rhs = Expr::app(const_("g"), Expr::bvar(0));
    let ty = Expr::pi(BinderInfo::Default, nat(), nat_eq(lhs, rhs));

    // A placeholder proof of the right *type* (its value is not re-checked under
    // add_decl_structural; the rewrite only needs the constant's type/name).
    let refl = Expr::const_(Name::from_string("Eq.refl"), vec![lvl1()]);
    let g_x = Expr::app(const_("g"), Expr::bvar(0));
    let refl_body = Expr::app(Expr::app(refl, nat()), g_x);
    let value = Expr::lam(BinderInfo::Default, nat(), refl_body);

    env.add_decl_structural(Declaration::Theorem {
        name: Name::from_string("fStuck.eq_def"),
        level_params,
        type_: ty,
        value,
    })
    .is_ok()
}

/// Imported `Acc`/`Acc.rec` + elaborated WF defs + the reducible equation lemma
/// `fInline.eq_def` (registered as a kernel `Theorem`).
fn env_with_imported_wf_and_eq_def() -> Environment {
    let mut env = imported_acc_env();
    elaborate_decls_into(&mut env, WF_DEFS);
    register_inline_eq_def(&mut env);

    let info = env
        .get_const(&Name::from_string("fInline.eq_def"))
        .expect("fInline.eq_def should be registered");
    let trust = info.trust_summary();
    assert!(
        trust.is_fully_verified(),
        "the imported WF equation lemma fInline.eq_def must itself be sorry-free \
         and axiom-free, got {trust:?}"
    );
    env
}

/// Full env with BOTH the reducible (`fInline`) and stuck (`fStuck`) WF defs and
/// both equation lemmas registered.
fn env_with_stuck_wf() -> Environment {
    let mut env = env_with_imported_wf_and_eq_def();
    assert!(
        register_stuck_wf_def(&mut env),
        "fStuck (over an Opaque accessibility witness) should register"
    );
    assert!(
        register_stuck_eq_def_structural(&mut env),
        "fStuck.eq_def should register structurally"
    );
    env
}

/// Drive `simp only [lemma]` on `goal_target`, returning
/// `(closed, fired, proof_opt)`:
/// - `closed`  — the tactic succeeded AND no goals remain;
/// - `fired`   — the closing proof references `lemma` (i.e. simp's matcher
///   actually applied the named lemma, as opposed to closing by def-eq);
/// - `proof_opt` — the closed proof term, for kernel re-checking.
fn run_simp_only(env: Environment, goal_target: Expr, lemma: &str) -> (bool, bool, Option<Expr>) {
    let mut state = ProofState::new(env, goal_target);
    let mut config = SimpConfig::new();
    config.only = true;
    config.extra_lemmas = vec![lemma.to_string()];
    let result = simp(&mut state, config);
    let closed = result.is_ok() && state.goals().is_empty();
    let proof = state.closed_proof();
    let fired = proof
        .as_ref()
        .map(|p| p.collect_constants().contains(&Name::from_string(lemma)))
        .unwrap_or(false);
    (closed, fired, proof)
}

// ---------------------------------------------------------------------------
// Precondition: the synthesized env is the genuine *import* configuration.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_wf_env_shape_is_genuine_import() {
    let env = env_with_imported_wf_and_eq_def();

    let rec = env
        .get_recursor(&Name::from_string("Acc.rec"))
        .expect("Acc.rec must be a registered recursor on import");
    assert_eq!(rec.num_params, 2, "Acc.rec: params = α, r");
    assert_eq!(rec.num_motives, 1, "Acc.rec: single motive");
    assert_eq!(rec.num_minors, 1, "Acc.rec: one minor (the Acc.intro case)");
    assert_eq!(rec.num_indices, 1, "Acc.rec: one index (the point)");
    assert_eq!(rec.arg_order, RecursorArgOrder::MajorAfterMinors);
    assert_eq!(
        rec.level_params.len(),
        2,
        "Acc.rec carries TWO universe params (large elimination from a Prop)"
    );

    assert!(
        env.get_const(&Name::from_string("WellFounded.fix"))
            .is_none(),
        "imported env must NOT have a clean-side WellFounded.fix"
    );

    assert!(
        env.get_recursor(&Name::from_string("fInline")).is_none(),
        "fInline must be a definition, not a registered recursor"
    );
    let fbody = env
        .get_const(&Name::from_string("fInline"))
        .and_then(|i| i.value.clone())
        .expect("fInline should have a definition body");
    assert!(
        fbody
            .collect_constants()
            .contains(&Name::from_string("Acc.rec")),
        "fInline's body must recurse through the imported Acc.rec, got: {:?}",
        fbody.collect_constants()
    );

    let eq_ty = env
        .get_const(&Name::from_string("fInline.eq_def"))
        .map(|i| i.type_.clone())
        .expect("fInline.eq_def should be registered");
    assert!(
        matches!(eq_ty.kind(), ExprKind::Pi(..)),
        "fInline.eq_def must be ∀-quantified, got {eq_ty:?}"
    );
}

// ---------------------------------------------------------------------------
// Control: the imported `fInline` (inlined Acc.intro) reduces by the kernel to
// the genuinely-correct value, while the imported `fStuck` (Opaque witness)
// does NOT — and `fStuck 4` is NOT def-eq to `g 4`. This isolates the two
// regimes the simp probes below distinguish.
// ---------------------------------------------------------------------------

#[test]
fn test_inline_reduces_but_stuck_does_not() {
    let env = env_with_stuck_wf();
    let tc = TypeChecker::new(&env);

    // fInline 4 -> Nat.add 4 4 = 8 (inlined Acc.intro lets Acc.rec fire).
    let inline4 = app_fn_at_zero(&env, "fInline", nat_lit(4));
    assert!(
        tc.is_def_eq(&inline4, &nat_lit(8)),
        "fInline 4 must iota-reduce through the imported Acc.rec to 8; got head {}",
        whnf_head(&env, &inline4)
    );

    // fStuck 4 is STUCK on Acc.rec (Opaque witness blocks iota).
    let stuck4 = app_fn_at_zero(&env, "fStuck", nat_lit(4));
    let head = whnf_head(&env, &stuck4);
    assert!(
        head == "Acc.rec" || head == "fStuck",
        "fStuck 4 must be stuck (head {head})"
    );

    // The decisive precondition: `fStuck 4` is NOT definitionally equal to its
    // equation RHS `g 4`. So a goal `fStuck 4 = g 4` can ONLY be closed by
    // actually firing the equation lemma — firing is fully observable.
    let g4 = Expr::app(const_("g"), nat_lit(4));
    assert!(
        !tc.is_def_eq(&stuck4, &g4),
        "fStuck 4 must NOT be def-eq to g 4 (the Opaque witness blocks reduction); \
         if it were, def-eq closure would mask whether the lemma fired"
    );
}

// ---------------------------------------------------------------------------
// MAIN VALIDATION (Probe S): `simp only [fStuck.eq_def]` over a GENUINELY STUCK
// use FIRES the imported equation lemma.
//
// Goal: fStuck 4 = g 4. Since `fStuck 4` is not def-eq to `g 4` (control above),
// the only path to closure is firing `fStuck.eq_def : ∀ x, fStuck x = g x`,
// which rewrites `fStuck 4` -> `g 4`, leaving `g 4 = g 4` closed by rfl. We
// assert the goal closes, the proof REFERENCES the lemma (firing, not def-eq),
// and the assembled proof kernel-checks and is sorry-free / axiom-free. This is
// the sharp test simp's reducible-use closure could not provide: simp's lemma
// matcher does NOT have the B53 `rw` defect on the realistic stuck shape.
// ---------------------------------------------------------------------------

#[test]
fn test_simp_only_fires_lemma_on_stuck_imported_use() {
    let env = env_with_stuck_wf();

    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fStuck", nat_lit(4)),
        Expr::app(const_("g"), nat_lit(4)),
    );
    let root_target = goal_target.clone();

    let (closed, fired, proof) = run_simp_only(env, goal_target, "fStuck.eq_def");
    assert!(
        closed,
        "simp only [fStuck.eq_def] must close `fStuck 4 = g 4` (a goal NOT \
         closable by def-eq) by firing the imported equation lemma"
    );
    assert!(
        fired,
        "the closing proof must REFERENCE fStuck.eq_def — proving simp's matcher \
         applied the named lemma rather than closing by def-eq (which is \
         impossible here: fStuck 4 is not def-eq to g 4)"
    );

    let proof = proof.expect("a closed simp proof state must yield a closed proof term");
    let env2 = env_with_stuck_wf();
    kernel_check_proof(&env2, &root_target, &proof);

    let trust = DeclarationTrustSummary::from_expr(&proof);
    assert!(
        !trust.has_sorry(),
        "simp's closing proof must be sorry-free, got {trust:?}"
    );
    assert_eq!(
        trust.trusted_axiom_count(),
        0,
        "simp's closing proof must carry no trusted axioms, got {trust:?}"
    );
}

// ---------------------------------------------------------------------------
// Negative control: WITHOUT the equation lemma named, `simp only []` CANNOT
// close the stuck goal (no def-eq masking is possible, since `fStuck 4` is not
// def-eq to `g 4`). This proves the closure in Probe S is genuinely the named
// lemma firing, not a coincidental def-eq through `fStuck`'s body.
// ---------------------------------------------------------------------------

#[test]
fn test_simp_only_without_lemma_cannot_close_stuck_use() {
    let env = env_with_stuck_wf();

    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fStuck", nat_lit(4)),
        Expr::app(const_("g"), nat_lit(4)),
    );
    let mut state = ProofState::new(env, goal_target);

    let mut config = SimpConfig::new();
    config.only = true; // no extra lemmas, no registry
    let result = simp(&mut state, config);

    assert!(
        !(result.is_ok() && state.goals().is_empty()),
        "simp only [] must NOT close `fStuck 4 = g 4` without the equation lemma \
         (the use is stuck and not def-eq to g 4); if it does, the firing in \
         Probe S is being masked by an unexpected def-eq closure"
    );
}

// ---------------------------------------------------------------------------
// Locked in (Probe R): for the REDUCIBLE `fInline`, `simp only [fInline.eq_def]`
// CLOSES `fInline 4 = g 4` SOUNDLY — by def-eq, since the use-site iota-reduces
// to the equation's RHS. The named lemma is redundant here (firing is
// unobservable and not required): `closed = true`, but it is acceptable that the
// proof close by `Eq.refl`. This documents WHY the reducible case cannot decide
// the matcher question (and why B53 left simp unchanged) while still pinning the
// sound closure. The assembled proof kernel-checks and is sorry-free / axiom-free
// regardless of whether the lemma fired.
// ---------------------------------------------------------------------------

#[test]
fn test_simp_only_reducible_use_closes_soundly_by_defeq() {
    let env = env_with_imported_wf_and_eq_def();

    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fInline", nat_lit(4)),
        Expr::app(const_("g"), nat_lit(4)),
    );
    let root_target = goal_target.clone();

    let (closed, _fired, proof) = run_simp_only(env, goal_target, "fInline.eq_def");
    assert!(
        closed,
        "simp only [fInline.eq_def] must close `fInline 4 = g 4` — soundly, by \
         def-eq (the reducible use is definitionally equal to its RHS)"
    );

    let proof = proof.expect("a closed simp proof state must yield a closed proof term");
    let env2 = env_with_imported_wf_and_eq_def();
    kernel_check_proof(&env2, &root_target, &proof);

    let trust = DeclarationTrustSummary::from_expr(&proof);
    assert!(
        !trust.has_sorry(),
        "the reducible-use closing proof must be sorry-free, got {trust:?}"
    );
    assert_eq!(
        trust.trusted_axiom_count(),
        0,
        "the reducible-use closing proof must carry no trusted axioms, got {trust:?}"
    );
}

// ---------------------------------------------------------------------------
// FLIP-ON-FIX pin: the reducible `fInline` use does NOT *fire* the named lemma —
// simp closes it by def-eq (the use reduces to the RHS), so the proof is a bare
// `Eq.refl` that does NOT reference `fInline.eq_def`. This is sound and is the
// documented, expected behavior (a reducible use is def-eq to the RHS, so the
// matcher whnf-reducing it away before binding `fInline ?x` is harmless — the
// def-eq closer succeeds anyway).
//
// Pinned (NOT `#[ignore]`d) so it flips to a failure IF simp's matcher is ever
// changed — e.g. via a B53-style keyed head-symbol pre-match — to ALSO fire the
// named lemma on a reducible use. That would not be wrong, but it is a deliberate
// behavior change with broad blast radius across simp; this pin makes such a
// change visible and forces a conscious re-evaluation (and a flip of this
// assertion to `fired == true`). The genuinely-stuck Probe S is the test that
// actually exercises simp's matcher firing.
// ---------------------------------------------------------------------------

#[test]
fn test_simp_reducible_use_closes_by_defeq_not_lemma_fire_pending() {
    let env = env_with_imported_wf_and_eq_def();

    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fInline", nat_lit(4)),
        Expr::app(const_("g"), nat_lit(4)),
    );

    let (closed, fired, _proof) = run_simp_only(env, goal_target, "fInline.eq_def");
    assert!(closed, "reducible use closes (by def-eq)");
    assert!(
        !fired,
        "FLIP-ON-FIX: simp now FIRES fInline.eq_def on a *reducible* use (proof \
         references the lemma). simp's matcher changed to keyed head-symbol \
         matching (à la the B53 `rw` fix) on reducible redexes. This is sound, \
         but a deliberate broad-blast-radius behavior change — flip this pin to \
         `fired == true`, re-run the full clean-elab --lib suite, and confirm no \
         simp normal-form regressions before landing."
    );
}

// ---------------------------------------------------------------------------
// Control: the NATIVE path — Clean's own `Acc` built in-process — produces the
// same stuck-use simp-firing behavior, confirming the imported-eliminator /
// imported-equation-lemma handling matches native byte-for-byte.
// ---------------------------------------------------------------------------

#[test]
fn test_native_simp_fires_lemma_on_stuck_use_matches_import() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env.init_eq().expect("init_eq");
    env.add_inductive(acc_decl()).expect("Acc should declare");

    elaborate_decls_into(&mut env, WF_DEFS);
    register_inline_eq_def(&mut env);
    assert!(register_stuck_wf_def(&mut env), "native fStuck registers");
    assert!(
        register_stuck_eq_def_structural(&mut env),
        "native fStuck.eq_def registers"
    );

    // Precondition: native fStuck 4 is stuck and not def-eq to g 4.
    {
        let tc = TypeChecker::new(&env);
        let stuck4 = app_fn_at_zero(&env, "fStuck", nat_lit(4));
        let g4 = Expr::app(const_("g"), nat_lit(4));
        assert!(
            !tc.is_def_eq(&stuck4, &g4),
            "native fStuck 4 must not be def-eq to g 4"
        );
    }

    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fStuck", nat_lit(4)),
        Expr::app(const_("g"), nat_lit(4)),
    );
    let root_target = goal_target.clone();
    let (closed, fired, proof) = run_simp_only(env, goal_target, "fStuck.eq_def");
    assert!(closed, "native simp only [fStuck.eq_def] should close");
    assert!(
        fired,
        "native proof must reference fStuck.eq_def (matcher fired, matching import)"
    );

    let proof = proof.expect("native closed proof");
    // Rebuild a fresh env to kernel-check against (run_simp_only consumed env).
    let mut env2 = Environment::new();
    env2.init_nat().expect("init_nat");
    env2.init_true_false().expect("init_true_false");
    env2.init_eq().expect("init_eq");
    env2.add_inductive(acc_decl()).expect("Acc should declare");
    elaborate_decls_into(&mut env2, WF_DEFS);
    register_inline_eq_def(&mut env2);
    register_stuck_wf_def(&mut env2);
    register_stuck_eq_def_structural(&mut env2);
    kernel_check_proof(&env2, &root_target, &proof);
}
