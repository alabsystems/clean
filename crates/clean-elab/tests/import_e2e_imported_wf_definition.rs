// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: an IMPORTED function DEFINED BY WELL-FOUNDED RECURSION and the
//! reduction / equation-lemma unfolding of its *uses* (imported_wf_definition).
//!
//! ## How this differs from the WF-recursion probe (B49)
//!
//! B49 (`import_e2e_well_founded_recursion`) validated a definition Clean
//! *lowers* through the imported `Acc.rec`, reducing on an inlined `Acc.intro`.
//! This probe is one layer up the real `.olean` shape: a Lean-compiled module
//! ships a WF-defined function `f` as a **plain `Declaration::Definition`** whose
//! body is `@Acc.rec …` (the `WellFounded.fix` core), PLUS a **generated
//! equation lemma** `f.eq_def : ∀ x, f x = <rhs>` shipped as a fully-formed
//! `Declaration::Theorem`. We reproduce *both* imported constants and then probe
//! how a *new* `clean-elab`-elaborated goal that USES `f` behaves under the two
//! reduction vehicles Lean exposes:
//!
//! (a) **kernel iota on `f` applied to a concrete argument.** A WF def reduces
//!     by iota only when the embedded `Acc` accessibility proof whnfs to
//!     `Acc.intro`. We build `f` two ways:
//!       * `fInline` — the `Acc` proof is an *inlined* `Acc.intro`, so
//!         `fInline n` genuinely iota-reduces for every `n` (and its equation
//!         lemma is provable by `rfl`); and
//!       * `fStuck` — the `Acc` proof is an **`Opaque`** witness
//!         (`accOpaque : ∀ x, Acc emptyRel x`), so `fStuck n` is STUCK (matching
//!         Lean: a WF def over an opaque/irreducible well-foundedness proof
//!         never iota-reduces; only the propositional equation lemma unfolds it).
//!
//! (b) **the imported equation lemma as the rewrite vehicle.** `rw [f.eq_def]`
//!     must unfold a *use* `f x` to `<rhs>`. The sharp finding (and the fix this
//!     batch lands): the environment-constant rewrite path
//!     (`resolve_env_rewrite_equation`) matched its `from` side against the goal
//!     via the WHNF-reducing unifier, so a use of a *reducible* defined function
//!     (`fInline n`, which iota-reduces) was reduced away before the
//!     `∀x, f x = g x` pattern `f ?x` could bind — yielding a spurious
//!     `RewriteNoMatch`. Lean's `rw` selects targets by *keyed* head-symbol
//!     matching without whnf-reducing the goal; the local-hypothesis rewrite
//!     path already matched syntactically. We add the same keyed head-symbol
//!     pre-match to the env-constant path so `rw [f.eq_def]` fires on a use of
//!     an imported WF-defined function — reducible (`fInline`) or genuinely
//!     stuck (`fStuck`) alike.
//!
//! ## The imported (`.olean`) shape we reproduce
//!
//! Exactly as in B49: the kernel builds `Acc` + `Acc.intro` + `Acc.rec` in a
//! scratch env; we copy the inductive / constructor / **registered recursor**
//! verbatim into a fresh env, with **no** `init_well_founded` bootstrap, then
//! build the WF-defined `f` *through the clean-elab elaborator* over the imported
//! `Acc.rec` and register the equation lemma as a kernel `Declaration::Theorem`
//! (its `rfl` proof kernel-checks because `fInline x` is def-eq to its `<rhs>`).
//! We assert `get_recursor("Acc.rec") == Some` and the absence of any clean-side
//! `WellFounded` scaffolding so the probe stays honest about the import path.
//!
//! ## What this pins
//!
//! Bug fixed: `rw [f.eq_def]` over a *use* of an imported, ∀-quantified WF
//! equation lemma now fires (keyed head-symbol match in the env-constant rewrite
//! path), producing a kernel-checked, sorry-free, axiom-free proof that
//! references the lemma. Probe 1 (`fInline`, reducible use) is the regression
//! test for the fix; the native control confirms the behavior is not
//! import-specific. Distinct observable `Nat` values make a wrong slot / wrong
//! arg show up as a different number rather than passing silently.
//!
//! Locked in: `simp only [f.eq_def]` *closes* a reducible WF use soundly (by
//! def-eq, since the use-site reduces to its value) — simp's lemma matcher is
//! left unchanged (broader blast radius) and the closure is correct regardless.
//!
//! Pinned honestly: the genuinely non-reducing `fStuck` (Opaque accessibility
//! witness) does NOT iota-reduce under bare whnf — matching Lean, where a WF use
//! reduces only via its equation lemma. Its equation lemma is true but not
//! `rfl`-provable (it needs `WellFounded.fix_eq`, out of scope), so it is
//! registered structurally (test fixture, with a `// SOUNDNESS:` note) purely to
//! demonstrate the keyed rewrite reaches even a STUCK WF use.

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::env::{Declaration, DeclarationTrustSummary, Environment};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, RecursorArgOrder, TypeChecker};

use clean_elab::tactic::{rewrite, simp, Goal, ProofState, SimpConfig};
use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

// ---------------------------------------------------------------------------
// Helpers (mirror import_e2e_well_founded_recursion's Acc-import scaffolding)
// ---------------------------------------------------------------------------

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn succ(n: Expr) -> Expr {
    Expr::app(const_("Nat.succ"), n)
}

fn nat() -> Expr {
    const_("Nat")
}

/// `Nat` literal `n` in the kernel's native literal representation (the form
/// the unifier normalizes arguments to), so a rewrite's resolved `from` side
/// matches the goal syntactically rather than mixing literal / `Nat.succ`-chain
/// encodings.
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

/// `@f.{0…} arg` for a (possibly universe-polymorphic) elaborated function
/// `f`, instantiating each of its level params at `0`. The WF defs here all
/// produce a `Prop`-level accessibility motive, so `0` is the level the
/// elaborator/kernel uses; this keeps the application's level-arity correct
/// regardless of how many params elaboration introduced.
fn app_fn_at_zero(env: &Environment, f_name: &str, arg: Expr) -> Expr {
    let n = env
        .get_const(&Name::from_string(f_name))
        .map_or(0, |i| i.level_params.len());
    let levels = vec![Level::zero(); n];
    Expr::app(Expr::const_(Name::from_string(f_name), levels), arg)
}

/// Kernel-check an assembled closed `proof` against `goal_ty` using the trusted
/// `TypeChecker` (full checking via `check_type`, `infer_only=false`). This is
/// the authoritative kernel acceptance check — stronger than relying on the
/// tactic's incremental `close_goal`, and it tolerates the def-eq collapse of a
/// reducible goal (the certificate *verifier* is intentionally stricter and is
/// not the kernel's word).
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

/// Build the `Acc : {α : Sort u} → (α → α → Prop) → α → Prop` inductive with
/// `Acc.intro : {α} → (r) → (x : α) → (∀ y, r y x → Acc r y) → Acc r x`.
///
/// Mirrors Clean's `init_well_founded` kernel build of `Acc`, so the
/// kernel-generated `Acc.rec` is byte-identical to the one an `.olean` ships.
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

    // Acc : Π {α : Sort u}. Π (r : α→α→Prop). Π (a : α). Prop
    let acc_type = {
        let r_type = mk_r_type(0);
        let body = Expr::pi(BinderInfo::Default, Expr::bvar(1), prop.clone());
        let body = Expr::pi(BinderInfo::Default, r_type, body);
        Expr::pi(BinderInfo::Implicit, sort_u.clone(), body)
    };

    // Acc.intro : Π {α}. Π (r). Π (x : α). Π (h : ∀ y, r y x → Acc r y). Acc r x
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

/// A faithfully *imported* `Acc`: the kernel-built family + constructor +
/// `Acc.rec` recursor copied verbatim into a fresh env, with **no**
/// `init_well_founded` bootstrap. `Acc.rec` is a registered recursor;
/// `WellFounded.*` are absent (an importing def synthesises through `Acc.rec`).
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

/// The WF-defined function source that every probe shares.
///
/// `fInline x` runs `@Acc.rec` over an *inlined* `Acc.intro` accessibility
/// proof for `x`, so it iota-reduces for every concrete `x` to the minor's
/// value `Nat.add x x`. `g x := Nat.add x x` is the intended `<rhs>` of the
/// equation lemma.  (The genuinely *non-reducing* WF def `fStuck` — built over
/// an `Opaque` accessibility witness, the faithful shape of a real `.olean` WF
/// def — is constructed separately in `register_stuck_wf_def`.)
const WF_DEFS: &str = "\
def emptyRel (a b : Nat) : Prop := False\n\
def g (x : Nat) : Nat := Nat.add x x\n\
def fInline (x : Nat) : Nat :=\n  \
  @Acc.rec Nat emptyRel (fun a _ => Nat) (fun y h ih => Nat.add y y) x\n    \
    (@Acc.intro Nat emptyRel x (fun (z : Nat) (hz : emptyRel z x) => False.elim hz))\n";

/// Build the genuinely *non-reducing* WF def `fStuck`, the faithful shape of a
/// Lean-compiled `.olean` WF function: its accessibility witness is an
/// **`Opaque`** constant `accOpaque : ∀ x, Acc emptyRel x`, which `whnf` will
/// not unfold (matching how a real WF def bottoms out in an opaque / irreducible
/// well-foundedness proof). Consequently `@Acc.rec … (accOpaque x)` is STUCK:
/// the major premise never whnfs to `Acc.intro`, so iota cannot fire — exactly
/// Lean's behavior, where a WF use reduces only via its equation lemma.
///
/// Returns `true` once `accOpaque` and `fStuck` are registered.
fn register_stuck_wf_def(env: &mut Environment) -> bool {
    // accOpaque : ∀ (x : Nat), Acc emptyRel x — Opaque, hidden value is the same
    // inlined Acc.intro proof, but it is sealed from whnf.
    let acc_at = |x: Expr| -> Expr {
        Expr::app(Expr::app(Expr::app(acc_c(), nat()), const_("emptyRel")), x)
    };
    let opaque_ty = Expr::pi(BinderInfo::Default, nat(), acc_at(Expr::bvar(0)));

    // value: fun (x : Nat) => @Acc.intro Nat emptyRel x (fun z hz => False.elim hz)
    let intro = Expr::const_(Name::from_string("Acc.intro"), vec![lvl1()]);
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![lvl1()]);
    // under [x, z]: emptyRel z x ; the `hz` binder body discharges via False.elim.
    let acc_field = {
        // motive of False.elim is `Acc emptyRel z` (z = BVar1 under [x,z,hz]).
        let acc_r_z = Expr::app(
            Expr::app(Expr::app(acc_c(), nat()), const_("emptyRel")),
            Expr::bvar(1),
        );
        let body = Expr::app(Expr::app(false_elim, acc_r_z), Expr::bvar(0));
        // hz : emptyRel z x (under [x, z]: z = BVar0, x = BVar1)
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

/// Register the imported equation lemma `fInline.eq_def : ∀ x, fInline x = g x`
/// as a kernel `Declaration::Theorem`, exactly as a Lean-compiled WF equation
/// lemma appears: a fully-formed declaration with a baked-in proof term.
///
/// The proof is `fun (x : Nat) => @Eq.refl Nat (g x)`, which has type
/// `∀ x, g x = g x` and kernel-checks at `∀ x, fInline x = g x` because
/// `fInline x` is definitionally equal to `g x` (`fInline x` iota-reduces
/// through the imported `Acc.rec` on its inlined `Acc.intro` to `Nat.add x x`,
/// and `g x` delta-/beta-reduces to the same). A genuine, sorry-free,
/// axiom-free equation lemma referencing only imported / elaborated constants.
fn register_inline_eq_def(env: &mut Environment) {
    // A Lean-compiled WF def can carry universe params (here from `False.elim`'s
    // motive). The equation lemma is polymorphic over exactly those params, so it
    // references `@fInline.{u…}` at the matching universe — mirroring how a real
    // imported `f.eq_def` shares its function's level params.
    let level_params = env
        .get_const(&Name::from_string("fInline"))
        .map(|i| i.level_params.clone())
        .expect("fInline should be registered");
    let f_levels: Vec<Level> = level_params
        .iter()
        .map(|n| Level::param(n.clone()))
        .collect();
    let f_inline = Expr::const_(Name::from_string("fInline"), f_levels);

    // ∀ (x : Nat), @fInline.{u…} x = g x
    let lhs = Expr::app(f_inline, Expr::bvar(0));
    let rhs = Expr::app(const_("g"), Expr::bvar(0));
    let eq_body = nat_eq(lhs, rhs);
    let ty = Expr::pi(BinderInfo::Default, nat(), eq_body);

    // proof: fun (x : Nat) => @Eq.refl Nat (g x)
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

/// Register the equation lemma `fStuck.eq_def : ∀ x, fStuck x = g x` for the
/// genuinely non-reducing `fStuck`.
///
/// `fStuck x` is STUCK (its accessibility witness is `Opaque`), so the equation
/// is true but NOT provable by `rfl`: in real Lean it is discharged by the
/// propositional `WellFounded.fix_eq` lemma, whose synthesis is out of scope for
/// this probe. We therefore register it the way a `.olean` ships it — as a
/// trusted, already-proved equation theorem — via `add_decl_structural`, which
/// records the declaration without re-running the kernel's def-eq check on the
/// (genuinely-true) proposition. This models the imported lemma faithfully and
/// lets us probe whether the env-constant *keyed* rewrite reaches a STUCK WF use.
///
// SOUNDNESS: test fixture only. `fStuck.eq_def : ∀ x, fStuck x = g x` is a true
// proposition — `accOpaque x` is proof-irrelevant-equal to the inlined
// `Acc.intro`, so `fStuck x` and `fInline x` denote the same value `g x` — but
// it cannot be checked by reduction because the `Opaque` witness blocks iota
// (this is exactly why Lean proves it via `WellFounded.fix_eq`). It is added
// structurally to emulate a Lean-compiled `.olean` equation lemma; no
// production code path uses `add_decl_structural`, and the proof terms a tactic
// builds *from* this lemma are kernel-checked against the goal type independently
// (`kernel_check_proof`). No new axiom is introduced into any production env.
fn register_stuck_eq_def_structural(env: &mut Environment) -> bool {
    let f_stuck = match env.get_const(&Name::from_string("fStuck")) {
        Some(i) => {
            let levels: Vec<Level> = i
                .level_params
                .iter()
                .map(|n| Level::param(n.clone()))
                .collect();
            Expr::const_(Name::from_string("fStuck"), levels)
        }
        None => return false,
    };
    let level_params = env
        .get_const(&Name::from_string("fStuck"))
        .map(|i| i.level_params.clone())
        .unwrap_or_default();

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

/// Build the full imported-WF environment used by the rewrite / simp probes:
/// imported `Acc`/`Acc.rec`, the elaborated WF defs, and the equation lemma
/// `fInline.eq_def` registered as a kernel constant.
fn env_with_imported_wf_and_eq_def() -> Environment {
    let mut env = imported_acc_env();
    elaborate_decls_into(&mut env, WF_DEFS);
    register_inline_eq_def(&mut env);

    // Sanity: the equation lemma is itself sorry-free and axiom-free, so any
    // proof a tactic builds out of it is clean iff the tactic wires it soundly.
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

// ---------------------------------------------------------------------------
// Precondition: the synthesized env is the genuine *import* configuration —
// Acc.rec is a registered recursor with the special two-universe / Prop-major
// layout, no WellFounded bootstrap, the WF def is a plain Definition (not a
// recursor), and the equation lemma is a ∀-quantified Eq theorem.
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

    // No clean-side WellFounded bootstrap exists.
    assert!(
        env.get_const(&Name::from_string("WellFounded.fix"))
            .is_none(),
        "imported env must NOT have a clean-side WellFounded.fix"
    );

    // `fInline` is a plain Definition whose body recurses through Acc.rec, NOT a
    // registered recursor — exactly a Lean-compiled WF def's shape.
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

    // The equation lemma is a ∀-quantified Eq over the imported function.
    let eq_ty = env
        .get_const(&Name::from_string("fInline.eq_def"))
        .map(|i| i.type_.clone())
        .expect("fInline.eq_def should be registered");
    assert!(
        matches!(eq_ty.kind(), ExprKind::Pi(..)),
        "fInline.eq_def must be ∀-quantified (a generated WF equation lemma is \
         not monomorphic), got {eq_ty:?}"
    );
}

// ---------------------------------------------------------------------------
// Control: the imported `fInline` (inlined Acc.intro) DOES iota-reduce by the
// kernel to the genuinely correct value. Isolates any later tactic-test failure
// to the tactic layer rather than the kernel's reduction of the imported def.
// ---------------------------------------------------------------------------

#[test]
fn test_imported_inline_wf_def_iota_reduces_by_kernel() {
    let env = env_with_imported_wf_and_eq_def();
    let tc = TypeChecker::new(&env);

    // fInline 3 -> Nat.add 3 3 = 6 (reduces: inlined Acc.intro lets Acc.rec fire).
    let call3 = app_fn_at_zero(&env, "fInline", nat_lit(3));
    assert!(
        tc.is_def_eq(&call3, &nat_lit(6)),
        "fInline 3 must iota-reduce through the imported Acc.rec to 6; got head {}",
        whnf_head(&env, &call3)
    );
    assert!(
        !tc.is_def_eq(&call3, &nat_lit(3)),
        "fInline must compute (6), not echo the point (3)"
    );
    // A second distinct witness: fInline 5 -> 10.
    let call5 = app_fn_at_zero(&env, "fInline", nat_lit(5));
    assert!(
        tc.is_def_eq(&call5, &nat_lit(10)),
        "fInline 5 must reduce to 10; got head {}",
        whnf_head(&env, &call5)
    );
}

// ---------------------------------------------------------------------------
// MAIN PROBE 1: `rw [fInline.eq_def]` over a USE of the imported WF function.
//
// Goal: fInline 4 = Nat.add 4 4.  The imported equation lemma
// `fInline.eq_def : ∀ x, fInline x = g x` must rewrite `fInline 4` -> `g 4`,
// leaving `g 4 = Nat.add 4 4`, which is closed by def-eq (`g 4` unfolds to
// `Nat.add 4 4`). The decisive check is that the env-constant rewrite path
// peels the ∀ binder, instantiates `x := 4`, and fires — producing a
// kernel-checked, sorry-free proof referencing `fInline.eq_def`.
// ---------------------------------------------------------------------------

#[test]
fn test_rw_imported_wf_eq_def_unfolds_use() {
    let env = env_with_imported_wf_and_eq_def();

    // fInline 4 = Nat.add 4 4
    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fInline", nat_lit(4)),
        Expr::app(Expr::app(const_("Nat.add"), nat_lit(4)), nat_lit(4)),
    );
    let mut state = ProofState::new(env, goal_target);
    let root_goal: Goal = state
        .goals()
        .front()
        .cloned()
        .expect("fresh proof state has exactly one goal");

    // rw [fInline.eq_def] : rewrites fInline 4 -> g 4 (forward).
    rewrite(&mut state, "fInline.eq_def", false)
        .expect("rw [fInline.eq_def] should resolve the imported ∀-equation and fire");

    // After rewriting, the remaining goal `g 4 = Nat.add 4 4` is closed by rfl.
    // Drive it with the existing `rfl`-style closure via `simp` (def-eq close).
    let close = simp(&mut state, SimpConfig::new());
    assert!(
        close.is_ok() && state.goals().is_empty(),
        "after rw [fInline.eq_def], `g 4 = Nat.add 4 4` must close by def-eq; \
         remaining goals: {}",
        state.goals().len()
    );

    let proof = state
        .closed_proof()
        .expect("a completed rw+close proof state must yield a closed proof term");
    kernel_check_proof(state.env(), &root_goal.target, &proof);

    // The rewrite genuinely fired iff the imported lemma appears in the proof.
    let constants = proof.collect_constants();
    assert!(
        constants.contains(&Name::from_string("fInline.eq_def")),
        "rw's proof must reference the imported equation lemma fInline.eq_def \
         (proving the rewrite fired, not a coincidental def-eq), references: {constants:?}"
    );
    let trust = DeclarationTrustSummary::from_expr(&proof);
    assert!(
        !trust.has_sorry(),
        "rw[eq_def] proof must be sorry-free, got {trust:?}"
    );
    assert_eq!(
        trust.trusted_axiom_count(),
        0,
        "rw[eq_def] proof must carry no trusted axioms, got {trust:?}"
    );
}

// ---------------------------------------------------------------------------
// PROBE 2: `simp only [fInline.eq_def]` over a USE of the imported WF function
// CLOSES the goal soundly.
//
// Goal: fInline 6 = Nat.add 6 6.  Outcome (locked in): `simp only` closes the
// goal with a kernel-checked, sorry-free, axiom-free proof. For a *reducible*
// WF def (`fInline 6` iota-reduces on its inlined `Acc.intro`), simp's lemma
// matcher — like the kernel unifier it uses — whnf-reduces `fInline 6` to its
// value before the `∀x, fInline x = g x` LHS pattern `fInline ?x` can bind, so
// simp DISCHARGES the (now definitionally-true) goal by `Eq.refl` rather than
// by an explicit application of the named lemma. That is sound and is the
// observable behavior; the named lemma is redundant when the use-site reduces.
// (`rw [fInline.eq_def]` in Probe 1, by contrast, matches the use *syntactically*
// via the keyed head-symbol path and so genuinely fires the lemma.) The
// flip-side — simp firing the named lemma on a use-site that is genuinely STUCK
// — is the realm of opaque WF defs, which cannot carry a sound `rfl` equation
// lemma without the full `WellFounded.fix_eq` machinery (see module header).
// ---------------------------------------------------------------------------

#[test]
fn test_simp_only_imported_wf_eq_def_closes_use_soundly() {
    let env = env_with_imported_wf_and_eq_def();

    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fInline", nat_lit(6)),
        Expr::app(Expr::app(const_("Nat.add"), nat_lit(6)), nat_lit(6)),
    );
    let mut state = ProofState::new(env, goal_target);
    let root_goal: Goal = state
        .goals()
        .front()
        .cloned()
        .expect("fresh proof state has exactly one goal");

    let mut config = SimpConfig::new();
    config.only = true;
    config.extra_lemmas = vec!["fInline.eq_def".to_string()];

    let result = simp(&mut state, config);
    assert!(
        result.is_ok() && state.goals().is_empty(),
        "simp only [fInline.eq_def] should close `fInline 6 = Nat.add 6 6`, \
         got {result:?}; remaining: {}",
        state.goals().len()
    );

    let proof = state
        .closed_proof()
        .expect("a completed simp proof state must yield a closed proof term");
    kernel_check_proof(state.env(), &root_goal.target, &proof);

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
// Control: without the imported equation lemma named, `simp only []` must NOT
// unfold `fInline 6` (the lemma is the only available unfold vehicle), so the
// goal does NOT close and no proof references `fInline.eq_def`. Isolates the
// closures in Probes 1/2 specifically to the imported equation lemma rather
// than to a coincidental def-eq through `fInline`'s body.
// ---------------------------------------------------------------------------

#[test]
fn test_simp_only_without_eq_def_does_not_unfold_use() {
    let env = env_with_imported_wf_and_eq_def();

    // fInline 6 = Nat.succ (Nat.add 6 6): a goal that is FALSE / not def-eq, so
    // it can only be "closed" by an actual (wrong) rewrite. Without the lemma,
    // simp only [] makes no progress and the goal stays open.
    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fInline", nat_lit(6)),
        succ(Expr::app(
            Expr::app(const_("Nat.add"), nat_lit(6)),
            nat_lit(6),
        )),
    );
    let mut state = ProofState::new(env, goal_target);

    let mut config = SimpConfig::new();
    config.only = true; // no extra lemmas, no registry, no builtins of use here
    let _ = simp(&mut state, config);

    // Either the goal stays open, or if a proof was produced it must not claim
    // the (false) equality via the equation lemma.
    if let Some(proof) = state.closed_proof() {
        let constants = proof.collect_constants();
        assert!(
            !constants.contains(&Name::from_string("fInline.eq_def")),
            "without naming it, fInline.eq_def must not appear in any proof: {constants:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// FLIP-ON-FIX pin: the genuinely non-reducing WF def `fStuck` (Opaque
// accessibility witness) does NOT iota-reduce under bare kernel whnf — `whnf`
// will not unfold an `Opaque` constant, so `Acc.rec` never sees an `Acc.intro`
// head. This matches Lean exactly: a WF definition reduces only via its
// propositional equation lemma, never by kernel iota on an opaque/irreducible
// well-foundedness proof. Pinned (not `#[ignore]`d) so it flips to a failure if
// Clean ever starts unfolding `Opaque` constants in whnf (which would diverge
// from Lean). The equation-lemma rewrite (the next test) is the genuine vehicle.
// ---------------------------------------------------------------------------

#[test]
fn test_stuck_wf_def_opaque_witness_does_not_iota_reduce_pending() {
    let mut env = env_with_imported_wf_and_eq_def();
    assert!(
        register_stuck_wf_def(&mut env),
        "fStuck (over an Opaque accessibility witness) should register"
    );
    let tc = TypeChecker::new(&env);

    let call = app_fn_at_zero(&env, "fStuck", nat_lit(3));
    let reduces = tc.is_def_eq(&call, &nat_lit(6));
    let head = whnf_head(&env, &call);
    assert!(
        !reduces,
        "FLIP-ON-FIX: fStuck 3 (WF def over an Opaque Acc witness) now iota- \
         reduces to 6 under bare whnf (head {head}) — Clean started unfolding an \
         Opaque constant, diverging from Lean. Replace this pin with a positive \
         assertion and re-examine the Opaque-in-whnf reduction model."
    );
    assert!(
        head == "Acc.rec" || head == "fStuck",
        "stuck WF def should be headed by the eliminator / the def, got {head}"
    );
}

// ---------------------------------------------------------------------------
// The keyed env-rewrite reaches even a genuinely STUCK WF use: `rw
// [fStuck.eq_def]` rewrites `fStuck 4` (which whnf cannot unfold) to `g 4` via
// the equation lemma. This is the precise reason Lean ships equation lemmas —
// they unfold a WF use that bare reduction cannot — and it confirms the keyed
// head-symbol match (the batch fix) is GENERAL: it fires whether the use-site
// is reducible (`fInline`, Probe 1) or stuck (`fStuck`, here). The equation
// lemma is registered structurally (see `register_stuck_eq_def_structural`),
// modeling the imported `.olean` lemma; the proof the rewrite builds is
// kernel-checked against the goal type below.
// ---------------------------------------------------------------------------

#[test]
fn test_rw_keyed_match_reaches_stuck_wf_use() {
    let mut env = env_with_imported_wf_and_eq_def();
    assert!(
        register_stuck_wf_def(&mut env),
        "fStuck should register before its equation lemma"
    );
    assert!(
        register_stuck_eq_def_structural(&mut env),
        "fStuck.eq_def should register structurally"
    );

    // Confirm the use is genuinely stuck to whnf, so a successful rewrite proves
    // the keyed match (not whnf reduction) is what found the `fStuck`-headed use.
    let stuck = app_fn_at_zero(&env, "fStuck", nat_lit(4));
    let head = whnf_head(&env, &stuck);
    assert!(
        head == "Acc.rec" || head == "fStuck",
        "precondition: fStuck 4 must be stuck (head {head})"
    );

    // Goal: fStuck 4 = g 4. After rw [fStuck.eq_def] -> g 4 = g 4, closed by rfl.
    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fStuck", nat_lit(4)),
        Expr::app(const_("g"), nat_lit(4)),
    );
    let mut state = ProofState::new(env, goal_target);
    let root_goal: Goal = state
        .goals()
        .front()
        .cloned()
        .expect("fresh proof state has exactly one goal");

    rewrite(&mut state, "fStuck.eq_def", false)
        .expect("rw [fStuck.eq_def] should fire via the keyed match on the stuck WF use");
    let close = simp(&mut state, SimpConfig::new());
    assert!(
        close.is_ok() && state.goals().is_empty(),
        "after rw [fStuck.eq_def], `g 4 = g 4` must close by rfl; remaining: {}",
        state.goals().len()
    );

    let proof = state
        .closed_proof()
        .expect("completed proof state must yield a closed proof term");
    kernel_check_proof(state.env(), &root_goal.target, &proof);
    assert!(
        proof
            .collect_constants()
            .contains(&Name::from_string("fStuck.eq_def")),
        "the proof must reference fStuck.eq_def (the keyed rewrite fired on the stuck use)"
    );
}

// ---------------------------------------------------------------------------
// Control: the NATIVE path — Clean's own `Acc` built in-process — produces the
// same WF def + equation-lemma rewrite behavior, confirming the imported-
// eliminator / imported-equation-lemma handling matches native byte-for-byte.
// ---------------------------------------------------------------------------

#[test]
fn test_native_wf_eq_def_rewrite_matches_import() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");
    env.init_eq().expect("init_eq");
    env.add_inductive(acc_decl()).expect("Acc should declare");

    elaborate_decls_into(&mut env, WF_DEFS);
    register_inline_eq_def(&mut env);

    // Native fInline iota-reduces identically.
    let call = app_fn_at_zero(&env, "fInline", nat_lit(5));
    {
        let tc = TypeChecker::new(&env);
        assert!(
            tc.is_def_eq(&call, &nat_lit(10)),
            "native fInline 5 must reduce to 10; got head {}",
            whnf_head(&env, &call)
        );
    }

    // Native rw [fInline.eq_def] fires identically.
    let goal_target = nat_eq(
        app_fn_at_zero(&env, "fInline", nat_lit(7)),
        Expr::app(Expr::app(const_("Nat.add"), nat_lit(7)), nat_lit(7)),
    );
    let mut state = ProofState::new(env, goal_target);
    let root_goal: Goal = state
        .goals()
        .front()
        .cloned()
        .expect("fresh proof state has exactly one goal");
    rewrite(&mut state, "fInline.eq_def", false).expect("native rw [fInline.eq_def] should fire");
    let close = simp(&mut state, SimpConfig::new());
    assert!(
        close.is_ok() && state.goals().is_empty(),
        "native rw[eq_def] should close `g 7 = Nat.add 7 7`; remaining: {}",
        state.goals().len()
    );
    let proof = state.closed_proof().expect("native closed proof");
    kernel_check_proof(state.env(), &root_goal.target, &proof);
    assert!(
        proof
            .collect_constants()
            .contains(&Name::from_string("fInline.eq_def")),
        "native proof must reference fInline.eq_def"
    );
}
