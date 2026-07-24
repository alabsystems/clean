// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! ck2 INGEST BRIDGE — first slice: `clean-kernel` artifact -> `clean-ck0`.
//!
//! GOAL (ck2 "one kernel, three kingdoms"): demonstrate that the minimal trust
//! root `clean-ck0` can INDEPENDENTLY re-check a real, already-`clean-kernel`-
//! checked artifact, so ck0 can inherit clean's verified corpus instead of
//! re-proving by hand.
//!
//! WHAT THIS TEST DOES:
//!  1. Builds a `clean-kernel` `Environment` with the `And` connective and pulls
//!     out the REAL artifacts clean's own kernel already accepted:
//!       * `And`           : the inductive (type + `And.intro` constructor),
//!       * `And.left/right` : the two projection definitions,
//!       * `And.symm`      : the theorem `{a b : Prop} -> And a b -> And b a`
//!         with proof `fun {a} {b} h => And.intro b a (And.right a b h)
//!         (And.left a b h)`.
//!  2. TRANSLATES (untrusted glue, this file only — `clean-ck0/src` is untouched)
//!     each clean `Expr`/`Level`/`Name` into a ck0 `RawExpr`/`RawLevel`/`Name`,
//!     failing CLOSED (explicit `BridgeError`) on anything outside the M0-M3
//!     fragment.
//!  3. Admits `And` via ck0 `add_inductive`, registers `And.left`/`And.right` as
//!     ck0 transparent defs, validates `And.symm`'s translated type + proof
//!     through ck0's chokepoint, and runs ck0 `check(proof, type)`.
//!  4. ck0 ACCEPTS — matching clean's verdict, decided entirely by ck0.
//!  5. GENUINENESS: a corrupted translation of the proof is REJECTED by ck0.
//!  6. FAITHFULNESS: the translated type/proof are the structural image of the
//!     clean artifact (not a degenerate constant) — asserted on shape + printed.
//!
//! FAITHFULNESS DISCIPLINE: if ck0 accepts a translation that does NOT
//! faithfully represent the clean artifact, that is a translator bug. The
//! translator is deliberately total-or-explicit-error and structure-preserving;
//! the corruption test (#5) shows the re-check is not a rubber stamp.

use clean_ck0::rawexpr::{BinderInfo as CkBinderInfo, RawLevel};
use clean_ck0::{
    add_inductive, Budget, Constructor as CkCtor, Env as CkEnv, InductiveDecl as CkIndDecl,
    MinimalEnv, Name as CkName, RawExpr, Term, Transparency,
};
use clean_kernel::{Declaration, Environment, Expr, ExprKind, Level as KLevel, Name as KName};

// ===========================================================================
// The untrusted translator: clean-kernel Expr/Level/Name -> ck0 RawExpr/...
// Handles EXACTLY the fragment the chosen artifact needs; everything else is a
// fail-closed `BridgeError`. (clean-ck0/src is NOT modified.)
// ===========================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum BridgeError {
    /// A clean `ExprKind` variant outside the M0-M3 fragment.
    UnsupportedExpr(String),
    /// A clean `Level` variant whose `Param` name is not in the decl telescope.
    UnknownLevelParam(String),
}

/// Map a clean universe-parameter `Name` to its positional index using the
/// declaration's `level_params` list (clean uses NAMED params; ck0 uses
/// POSITIONAL indices — this is a core representation-gap bridge point).
fn level_param_index(lps: &[KName], name: &KName) -> Option<u32> {
    lps.iter()
        .position(|p| p == name)
        .and_then(|i| u32::try_from(i).ok())
}

/// Translate a clean `Level` into a ck0 `RawLevel` against the decl's level
/// telescope `lps`. Fail-closed on unknown param / unsupported variant.
fn tr_level(lvl: &KLevel, lps: &[KName]) -> Result<RawLevel, BridgeError> {
    match lvl {
        KLevel::Zero => Ok(RawLevel::Zero),
        KLevel::Succ(l) => Ok(RawLevel::Succ(Box::new(tr_level(l, lps)?))),
        KLevel::Max(a, b) => Ok(RawLevel::Max(
            Box::new(tr_level(a, lps)?),
            Box::new(tr_level(b, lps)?),
        )),
        KLevel::IMax(a, b) => Ok(RawLevel::IMax(
            Box::new(tr_level(a, lps)?),
            Box::new(tr_level(b, lps)?),
        )),
        KLevel::Param(n) => level_param_index(lps, n)
            .map(RawLevel::Param)
            .ok_or_else(|| BridgeError::UnknownLevelParam(n.to_string())),
    }
}

/// The recursor-name suffixes ck0's chokepoint reserves for `Elim` (it REJECTS
/// these in `Const` position). The bridge mirrors that classification so a
/// recursor reference would be lowered to `RawExpr::Elim` rather than silently
/// mistranslated. The chosen artifact contains none, but we fail-closed loudly
/// if one appears (it needs the motive level, which a bare `Const` lacks).
fn is_recursor_suffix(last: &str) -> bool {
    matches!(
        last,
        "rec" | "recOn" | "casesOn" | "below" | "ibelow" | "brecOn" | "binductionOn" | "brecOnEq"
    )
}

fn tr_binfo(info: clean_kernel::expr::BinderInfo) -> CkBinderInfo {
    match info {
        clean_kernel::expr::BinderInfo::Default => CkBinderInfo::Default,
        clean_kernel::expr::BinderInfo::Implicit => CkBinderInfo::Implicit,
        clean_kernel::expr::BinderInfo::StrictImplicit => CkBinderInfo::StrictImplicit,
        clean_kernel::expr::BinderInfo::InstImplicit => CkBinderInfo::InstImplicit,
    }
}

/// Translate a clean `Name` (dotted, e.g. `And.intro`) to a ck0 `Name`.
fn tr_name(n: &KName) -> CkName {
    CkName::from_dotted(&n.to_string())
}

/// Translate a clean `Expr` to a ck0 `RawExpr`, against the level telescope
/// `lps`. Total over the fragment; fail-closed everywhere else.
fn tr_expr(e: &Expr, lps: &[KName]) -> Result<RawExpr, BridgeError> {
    match e.kind() {
        ExprKind::BVar(i) => Ok(RawExpr::BVar(*i)),
        ExprKind::Sort(l) => Ok(RawExpr::Sort(tr_level(l, lps)?)),
        ExprKind::Const(name, levels) => {
            if let Some(last) = name.last_component() {
                if is_recursor_suffix(&last) {
                    // A recursor reference cannot be faithfully lowered as a bare
                    // Const (it needs a motive level). The chosen artifact has
                    // none; fail closed rather than mistranslate.
                    return Err(BridgeError::UnsupportedExpr(format!(
                        "recursor `{name}` in Const position (needs Elim lowering)"
                    )));
                }
            }
            let lv: Result<Vec<RawLevel>, BridgeError> =
                levels.iter().map(|l| tr_level(l, lps)).collect();
            Ok(RawExpr::Const(tr_name(name), lv?))
        }
        ExprKind::App(f, a) => Ok(RawExpr::App(
            Box::new(tr_expr(f, lps)?),
            Box::new(tr_expr(a, lps)?),
        )),
        ExprKind::Lam(bd, ty, body) => Ok(RawExpr::Lam(
            tr_binfo(bd.info),
            Box::new(tr_expr(ty, lps)?),
            Box::new(tr_expr(body, lps)?),
        )),
        ExprKind::Pi(bd, ty, body) => Ok(RawExpr::Pi(
            tr_binfo(bd.info),
            Box::new(tr_expr(ty, lps)?),
            Box::new(tr_expr(body, lps)?),
        )),
        ExprKind::Let(_name, ty, val, body, _nondep) => Ok(RawExpr::Let(
            Box::new(tr_expr(ty, lps)?),
            Box::new(tr_expr(val, lps)?),
            Box::new(tr_expr(body, lps)?),
        )),
        ExprKind::Proj(name, idx, inner) => Ok(RawExpr::Proj(
            tr_name(name),
            *idx,
            Box::new(tr_expr(inner, lps)?),
        )),
        // Everything else is OUTSIDE this slice's fragment — fail closed.
        other => Err(BridgeError::UnsupportedExpr(format!("{other:?}"))),
    }
}

// ===========================================================================
// Helpers to lift a clean inductive / definition into ck0.
// ===========================================================================

/// Count the leading Pi binders of a (validated) ck0 `Term` — used to size the
/// constructor's field telescope when registering it as a ck0 def's type.
fn validate_closed(env: &dyn CkEnv, raw: &RawExpr) -> Term {
    Term::validate_closed(env, raw).expect("translated term validates through ck0 chokepoint")
}

/// Validate a translated term over `level_arity` universe params.
fn validate_lvl(env: &dyn CkEnv, raw: &RawExpr, level_arity: u32) -> Term {
    Term::validate(env, raw, 0, level_arity).expect("translated term validates (with level params)")
}

// ===========================================================================
// THE BRIDGE TEST
// ===========================================================================

/// Pull the real `And` inductive + `And.left/right` defs + `And.symm` theorem
/// out of a live clean-kernel environment.
struct CleanArtifacts {
    and_type: Expr,
    and_intro_type: Expr,
    and_left_type: Expr,
    and_left_value: Expr,
    and_right_type: Expr,
    and_right_value: Expr,
    symm_type: Expr,
    symm_value: Expr,
}

fn pull_clean_artifacts() -> CleanArtifacts {
    let mut env = Environment::new();
    env.init_and().expect("init_and");

    let get_ty = |env: &Environment, s: &str| {
        env.get_const(&KName::from_string(s))
            .unwrap_or_else(|| panic!("{s} present"))
            .type_
            .clone()
    };
    let get_val = |env: &Environment, s: &str| {
        env.get_const(&KName::from_string(s))
            .unwrap_or_else(|| panic!("{s} present"))
            .value
            .clone()
            .unwrap_or_else(|| panic!("{s} has a value"))
    };

    CleanArtifacts {
        and_type: get_ty(&env, "And"),
        and_intro_type: get_ty(&env, "And.intro"),
        and_left_type: get_ty(&env, "And.left"),
        and_left_value: get_val(&env, "And.left"),
        and_right_type: get_ty(&env, "And.right"),
        and_right_value: get_val(&env, "And.right"),
        symm_type: get_ty(&env, "And.symm"),
        symm_value: get_val(&env, "And.symm"),
    }
}

/// Build the ck0 env that re-checks `And.symm`: admit `And`, register the two
/// projection defs. Returns the env plus the translated symm type and proof.
fn build_ck0_env_and_symm(a: &CleanArtifacts) -> (MinimalEnv, Term, Term) {
    let lps: Vec<KName> = vec![]; // And + And.symm have no universe params.

    // --- (a) Admit `And` into ck0 via add_inductive. ---
    // The inductive + constructor types must validate against a bootstrap env
    // that knows the names (exactly the producer->kernel boundary).
    let boot = MinimalEnv::new()
        .with_const(CkName::from_dotted("And"), 0)
        .with_const(CkName::from_dotted("And.intro"), 0);

    let and_ty_raw = tr_expr(&a.and_type, &lps).expect("translate And type");
    let and_intro_raw = tr_expr(&a.and_intro_type, &lps).expect("translate And.intro type");
    let and_ty = validate_closed(&boot, &and_ty_raw);
    let and_intro_ty = validate_closed(&boot, &and_intro_raw);

    let ind = CkIndDecl {
        name: CkName::from_dotted("And"),
        num_level_params: 0,
        num_params: 2,
        type_: and_ty,
        constructors: vec![CkCtor {
            name: CkName::from_dotted("And.intro"),
            type_: and_intro_ty,
        }],
    };
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, ind).expect("ck0 admits And + derives And.rec");

    // --- (b) Register And.left / And.right as ck0 transparent defs. ---
    // Their bodies use Proj(And, 0/1, h); ck0 reduces proj-of-constructor in
    // def_eq (M1), so And.symm's proof can be checked by unfolding them.
    let left_ty_raw = tr_expr(&a.and_left_type, &lps).expect("tr And.left type");
    let left_val_raw = tr_expr(&a.and_left_value, &lps).expect("tr And.left value");
    let right_ty_raw = tr_expr(&a.and_right_type, &lps).expect("tr And.right type");
    let right_val_raw = tr_expr(&a.and_right_value, &lps).expect("tr And.right value");

    let left_ty = validate_closed(&env, &left_ty_raw);
    let left_val = validate_closed(&env, &left_val_raw);
    let right_ty = validate_closed(&env, &right_ty_raw);
    let right_val = validate_closed(&env, &right_val_raw);

    let env = env
        .with_def(
            CkName::from_dotted("And.left"),
            0,
            left_ty,
            left_val,
            Transparency::Transparent,
        )
        .with_def(
            CkName::from_dotted("And.right"),
            0,
            right_ty,
            right_val,
            Transparency::Transparent,
        );

    // --- (c) Translate And.symm's type + proof and validate them. ---
    let symm_ty_raw = tr_expr(&a.symm_type, &lps).expect("tr And.symm type");
    let symm_val_raw = tr_expr(&a.symm_value, &lps).expect("tr And.symm value");
    let symm_ty = validate_lvl(&env, &symm_ty_raw, 0);
    let symm_val = validate_lvl(&env, &symm_val_raw, 0);

    (env, symm_ty, symm_val)
}

#[test]
fn ck0_independently_rechecks_clean_and_symm() {
    let a = pull_clean_artifacts();
    let (env, symm_ty, symm_proof) = build_ck0_env_and_symm(&a);

    // THE HEADLINE: ck0 decides, on its own, that the proof checks against the
    // type — matching clean's verdict.
    let mut budget = Budget::default_budget();
    clean_ck0::check(&env, &symm_proof, &symm_ty, &mut budget)
        .expect("ck0 INDEPENDENTLY re-checks clean's And.symm: proof : type");

    // Sanity: the type is itself a well-formed proposition in ck0 (infers a
    // sort), so the check above is a real typing, not a vacuous pass.
    let mut budget2 = Budget::default_budget();
    let inferred_ty =
        clean_ck0::infer(&env, &symm_proof, &mut budget2).expect("ck0 infers a type for the proof");
    let mut budget3 = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&env, &inferred_ty, &symm_ty, &mut budget3).expect("def_eq"),
        "ck0's inferred type is def-eq to the translated clean type"
    );
}

#[test]
fn ck0_rejects_corrupted_translation_of_and_symm() {
    // GENUINENESS: tamper the proof so it is NO LONGER a proof of the stated
    // type, and confirm ck0's check FAILS. The corruption swaps the two
    // conjuncts in the And.intro head so the proof builds `And a b` while the
    // stated type demands `And b a` (a real type mismatch, not a syntax error).
    let a = pull_clean_artifacts();
    let lps: Vec<KName> = vec![];

    // Build the genuine env first (admits And, registers projections).
    let (env, symm_ty, good_proof) = build_ck0_env_and_symm(&a);

    // Sanity: the GOOD proof checks (so the corruption is the only difference).
    let mut b0 = Budget::default_budget();
    clean_ck0::check(&env, &good_proof, &symm_ty, &mut b0).expect("good proof checks");

    // Corrupt the clean proof term: in `And.intro b a (..) (..)`, swap the two
    // explicit args so it becomes `And.intro b a (And.left ..) (And.right ..)`,
    // i.e. the left/right witnesses are exchanged -> proves the wrong thing.
    let corrupt_val = corrupt_swap_intro_args(&a.and_symm_value());
    let corrupt_raw = tr_expr(&corrupt_val, &lps).expect("tr corrupted proof");
    let corrupt_proof = Term::validate(&env, &corrupt_raw, 0, 0).expect("corrupt validates");

    // It must NOT be the good proof (the corruption actually changed the term).
    assert_ne!(
        corrupt_proof, good_proof,
        "corruption must change the proof term"
    );

    let mut b1 = Budget::default_budget();
    let r = clean_ck0::check(&env, &corrupt_proof, &symm_ty, &mut b1);
    assert!(
        r.is_err(),
        "ck0 must REJECT the corrupted proof against And.symm's type: got {r:?}"
    );
}

impl CleanArtifacts {
    fn and_symm_value(&self) -> Expr {
        self.symm_value.clone()
    }
}

/// Swap the two explicit (proof) arguments of the outer `And.intro` application
/// in And.symm's proof body. The clean proof is
///   `fun {a}{b} h => And.intro b a (And.right a b h) (And.left a b h)`.
/// We rewrite it to `And.intro b a (And.left a b h) (And.right a b h)`, which is
/// a proof of `And b a` only if `And.left/right` were swapped — i.e. it now
/// proves the WRONG proposition and must be rejected.
fn corrupt_swap_intro_args(value: &Expr) -> Expr {
    // value = Lam(Lam(Lam(body))); descend to the body, swap, rebuild.
    if let ExprKind::Lam(b1, t1, body1) = value.kind() {
        if let ExprKind::Lam(b2, t2, body2) = body1.kind() {
            if let ExprKind::Lam(b3, t3, body3) = body2.kind() {
                let swapped = swap_app_last_two(body3);
                return Expr::lam(
                    *b1,
                    (**t1).clone(),
                    Expr::lam(*b2, (**t2).clone(), Expr::lam(*b3, (**t3).clone(), swapped)),
                );
            }
        }
    }
    panic!("And.symm proof was not the expected triple-lambda shape");
}

/// Given `App(App(head2, x), y)`, return `App(App(head2, y), x)` — swap the last
/// two application arguments. (head2 here is `And.intro b a`.)
fn swap_app_last_two(e: &Expr) -> Expr {
    if let ExprKind::App(f, y) = e.kind() {
        if let ExprKind::App(g, x) = f.kind() {
            return Expr::app(Expr::app((**g).clone(), (**y).clone()), (**x).clone());
        }
    }
    panic!("And.symm proof body was not a 2-arg And.intro application");
}

#[test]
fn translation_is_faithful_not_degenerate() {
    // FAITHFULNESS: the translated type/proof are the structural image of the
    // clean artifact — same binder shape, same heads — not a constant/trivial
    // stand-in. We assert structural landmarks on the ck0 RawExpr and print both
    // sides for the record.
    let a = pull_clean_artifacts();
    let lps: Vec<KName> = vec![];

    let symm_ty_raw = tr_expr(&a.symm_type, &lps).expect("tr type");
    let symm_val_raw = tr_expr(&a.symm_value, &lps).expect("tr value");

    // Type shape: Pi {a:Prop} Pi {b:Prop} Pi (h: And a b). And b a
    // -> three nested Pis; innermost codomain head is `And`.
    let (pi_count_ty, ty_head) = count_pis_and_head(&symm_ty_raw);
    assert_eq!(pi_count_ty, 3, "And.symm type has exactly 3 Pi binders");
    assert_eq!(
        ty_head,
        Some("And".to_string()),
        "And.symm type codomain head is `And`"
    );

    // Proof shape: three nested Lams; body head is `And.intro`.
    let (lam_count, body_head) = count_lams_and_head(&symm_val_raw);
    assert_eq!(lam_count, 3, "And.symm proof has exactly 3 Lam binders");
    assert_eq!(
        body_head,
        Some("And.intro".to_string()),
        "And.symm proof body head is the `And.intro` constructor"
    );

    // The proof references BOTH And.left and And.right (the genuine witnesses).
    let names = collect_const_names(&symm_val_raw);
    assert!(names.contains("And.intro"), "proof uses And.intro");
    assert!(names.contains("And.left"), "proof uses And.left");
    assert!(names.contains("And.right"), "proof uses And.right");

    // For the record (visible with --nocapture): clean side vs ck0 side.
    println!("CLEAN And.symm TYPE : {:?}", a.symm_type.kind());
    println!("ck0   And.symm TYPE : {symm_ty_raw:?}");
    println!("CLEAN And.symm PROOF: {:?}", a.symm_value.kind());
    println!("ck0   And.symm PROOF: {symm_val_raw:?}");
}

// --- small structural inspectors over ck0 RawExpr (test-local) ---

fn count_pis_and_head(e: &RawExpr) -> (u32, Option<String>) {
    let mut n = 0u32;
    let mut cur = e;
    while let RawExpr::Pi(_, _, codom) = cur {
        n += 1;
        cur = codom;
    }
    (n, raw_head_const(cur))
}

fn count_lams_and_head(e: &RawExpr) -> (u32, Option<String>) {
    let mut n = 0u32;
    let mut cur = e;
    while let RawExpr::Lam(_, _, body) = cur {
        n += 1;
        cur = body;
    }
    (n, raw_head_const(cur))
}

/// The head constant name of an application spine, if the head is a `Const`.
fn raw_head_const(e: &RawExpr) -> Option<String> {
    let mut cur = e;
    while let RawExpr::App(f, _) = cur {
        cur = f;
    }
    match cur {
        RawExpr::Const(n, _) => Some(format!("{n}")),
        _ => None,
    }
}

fn collect_const_names(e: &RawExpr) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    let mut stack = vec![e];
    while let Some(node) = stack.pop() {
        match node {
            RawExpr::Const(n, _) => {
                out.insert(format!("{n}"));
            }
            RawExpr::App(f, x) => {
                stack.push(f);
                stack.push(x);
            }
            RawExpr::Lam(_, t, b) | RawExpr::Pi(_, t, b) => {
                stack.push(t);
                stack.push(b);
            }
            RawExpr::Let(t, v, b) => {
                stack.push(t);
                stack.push(v);
                stack.push(b);
            }
            RawExpr::Proj(_, _, inner) => stack.push(inner),
            _ => {}
        }
    }
    out
}
