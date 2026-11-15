// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VF4's re-check by the quorum Q (`docs/DECISIONS.md` R162; Trust's proven-core
//! plan §2.0): every member of Q that exists today accepts, from the same
//! exported bytes, `chk_LIA_sound`, `chk_LIA_cases_sound`, the statement pin and
//! every F1 certificate, and refuses a forged one.
//!
//! Q is K* (from KR3), `clean-ck0` built by stock rustc, Lean 4's kernel, and an
//! externally written checker (from KR6). Two exist:
//!
//! * **Lean 4's kernel**: the pinned `leanchecker --fresh` replays every module
//!   of the theory (`ChkLIA`, `ChkLIASpec`, `ChkLIACases`), the corpus
//!   (`ChkLIAF1`) and the honest twin (`ChkLIAHonest`) from their `.olean`
//!   bytes, imports included, and must exit 0; `ChkLIAForged` (an `= false`
//!   twin of `f1_025` written with Lean's kernel bypassed) must exit 1 with a
//!   declaration type mismatch.
//! * **`clean-ck0`**: the declarations Clean's loader reads from the same
//!   `.olean` bytes are translated into ck0's raw syntax and admitted into a ck0
//!   environment built from EMPTY in dependency order: every inductive through
//!   ck0's own admission (`add_inductive`, ck0 derives and checks its
//!   recursor), every definition and theorem only after `clean_ck0::check(value
//!   : type)`, an axiom only when it is one of Ax0 by name AND its loaded type is
//!   definitionally Ax0's statement written in this file (`ax0_statement`; a
//!   tampered `propext` is the negative control), the four quotient formers as
//!   ck0's built-ins. Each subject is
//!   then checked by ck0 and its inferred type compared with the declared one.
//!   The forged twin must fail `check` with `TypeMismatch`; the honest twin must
//!   pass.
//!
//! "Built by stock rustc" is a property of the run, not of this file: R162
//! records the `rustup run stable cargo test` invocation that built it. Under
//! the workspace's Trust toolchain the same test runs as an ordinary test.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use clean_ck0::rawexpr::{BinderInfo as CkBinderInfo, RawLevel};
use clean_ck0::{
    add_inductive, add_inductive_mutual, add_inductive_nested, BigNat as CkBigNat, Budget,
    Constructor as CkCtor, InductiveDecl as CkIndDecl, MinimalEnv, MutualBlock, Name as CkName,
    QuotKind as CkQuotKind, RawExpr, RawLit, Term, Transparency,
};
use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind, Literal};
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, InductiveType, Level, QuotKind};
use clean_olean::load_module_with_deps;
use clean_olean::test_support::compiled_fixture_dir;

const PINNED: &str = "v4.30.0-rc2";
const FAMILY: &str = "chk_lia_f1";
const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];
/// The modules Lean's kernel replays (and must accept).
const ACCEPTED_MODULES: [&str; 5] = [
    "ChkLIA",
    "ChkLIASpec",
    "ChkLIACases",
    "ChkLIAF1",
    "ChkLIAHonest",
];
const FORGED_MODULE: &str = "ChkLIAForged";
/// ck0's fuel per decision. Its default (10^6 steps, sized for its own corpus)
/// runs out on `Nat.mul_comm`'s structural-recursion proof; a refusal for fuel
/// is still a refusal, so a larger bound changes no verdict's direction.
const CK0_FUEL: u64 = 100_000_000;
const FORGED: &str = "ChkLIAForged.f1_025_false";
const HONEST: &str = "ChkLIAHonest.f1_025_true";
/// The statements Q re-checks (with every F1 and census certificate of the
/// corpus module, found by prefix).
const SUBJECTS: [&str; 5] = [
    "ChkLIA.chk_LIA_sound",
    "ChkLIA.chk_LIA_cases_sound",
    "ChkLIASpec.statement_pin",
    "ChkLIASpec.spec_sound",
    "ChkLIA.u8_add_no_overflow",
];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn pinned_bin_dir() -> PathBuf {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this fixture is compiled by {PINNED}; the workspace pin moved"
    );
    let lean = clean_olean::pinned_lean_binary().expect("the pinned Lean toolchain");
    lean.parent().expect("bin/").to_path_buf()
}

// ===========================================================================
// Member 1: Lean 4's kernel (`leanchecker --fresh`).
// ===========================================================================

/// `(exit code, stderr)` of `leanchecker --fresh <module>` over `dir`.
fn leanchecker(bin: &Path, dir: &Path, module: &str) -> (Option<i32>, String) {
    // `leanchecker` asks `lean --print-prefix`; the pinned `bin/` goes first on
    // PATH so a `lean` earlier on it (a wrapper) is not the one asked.
    let path = std::env::var_os("PATH").unwrap_or_default();
    let mut dirs = vec![bin.to_path_buf()];
    dirs.extend(std::env::split_paths(&path));
    let out = Command::new(bin.join("leanchecker"))
        .arg("--fresh")
        .arg(module)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .env("PATH", std::env::join_paths(dirs).expect("PATH"))
        .output()
        .expect("run leanchecker");
    (
        out.status.code(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

// ===========================================================================
// Member 2: clean-ck0, from EMPTY.
// ===========================================================================

/// Why the translation stopped: it fails closed, never approximates.
enum BridgeError {
    Unsupported(String),
    UnknownLevelParam(String),
    Missing(String),
}

impl std::fmt::Debug for BridgeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(s) => write!(f, "unsupported: {s}"),
            Self::UnknownLevelParam(s) => write!(f, "unknown level parameter {s}"),
            Self::Missing(s) => write!(f, "missing constant {s}"),
        }
    }
}

/// The last components ck0 reserves for eliminators (`validate.rs`,
/// `is_recursor_name`): a constant so named must arrive as an `Elim`.
const CK0_ELIM_SUFFIXES: [&str; 8] = [
    "rec",
    "recOn",
    "casesOn",
    "below",
    "ibelow",
    "brecOn",
    "binductionOn",
    "brecOnEq",
];
/// The component appended to a Lean DEFINITION whose name ck0 reserves.
const AUX_DEF_COMPONENT: &str = "lean_aux_def";

/// ck0's name for `x`. In Lean, `List.below`, `List.brecOn`, `Nat.casesOn` and
/// the like are ordinary definitions (their values are checked below like any
/// other), but ck0 refuses every constant whose last component is an eliminator
/// suffix unless it arrives as its `Elim` (closing a level-arity bypass for a
/// constant that IS a recursor). A true recursor (`X.rec`) becomes `Elim` in
/// [`tr_expr`]; a definition so named gets one more component
/// (`List.below.lean_aux_def`). The renaming is injective (the test asserts no
/// Lean constant holds a renamed name) and applied everywhere the name occurs,
/// so the translated environment is the loaded one up to names.
fn tr_name(x: &Name) -> CkName {
    let s = x.to_string();
    let last = s.rsplit('.').next().unwrap_or(&s);
    if CK0_ELIM_SUFFIXES.contains(&last) {
        CkName::from_dotted(&format!("{s}.{AUX_DEF_COMPONENT}"))
    } else {
        CkName::from_dotted(&s)
    }
}

fn tr_level(l: &Level, lps: &[Name]) -> Result<RawLevel, BridgeError> {
    Ok(match l {
        Level::Zero => RawLevel::Zero,
        Level::Succ(a) => RawLevel::Succ(Box::new(tr_level(a, lps)?)),
        Level::Max(a, b) => RawLevel::Max(Box::new(tr_level(a, lps)?), Box::new(tr_level(b, lps)?)),
        Level::IMax(a, b) => {
            RawLevel::IMax(Box::new(tr_level(a, lps)?), Box::new(tr_level(b, lps)?))
        }
        Level::Param(p) => RawLevel::Param(
            lps.iter()
                .position(|q| q == p)
                .and_then(|i| u32::try_from(i).ok())
                .ok_or_else(|| BridgeError::UnknownLevelParam(p.to_string()))?,
        ),
    })
}

fn tr_binfo(b: BinderInfo) -> CkBinderInfo {
    match b {
        BinderInfo::Default => CkBinderInfo::Default,
        BinderInfo::Implicit => CkBinderInfo::Implicit,
        BinderInfo::StrictImplicit => CkBinderInfo::StrictImplicit,
        BinderInfo::InstImplicit => CkBinderInfo::InstImplicit,
    }
}

/// Clean's kernel expression → ck0's raw syntax. A recursor constant becomes
/// ck0's eliminator of its inductive (ck0 derives the full level vector); every
/// other constant stays a constant. Fails closed on any other node.
fn tr_expr(env: &Environment, e: &Expr, lps: &[Name]) -> Result<RawExpr, BridgeError> {
    Ok(match e.kind() {
        ExprKind::BVar(i) => RawExpr::BVar(*i),
        ExprKind::Sort(l) => RawExpr::Sort(tr_level(l, lps)?),
        ExprKind::Const(name, levels) => {
            let levels = levels
                .iter()
                .map(|l| tr_level(l, lps))
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(rec) = env.get_recursor(name) {
                let ind = env
                    .get_inductive(&rec.inductive_name)
                    .ok_or_else(|| BridgeError::Missing(rec.inductive_name.to_string()))?;
                if rec.name != Name::from_string(&format!("{}.rec", rec.inductive_name)) {
                    return Err(BridgeError::Unsupported(format!(
                        "auxiliary recursor {name}"
                    )));
                }
                let motive_levels = rec.level_params.len() - ind.level_params.len();
                let (m, rest) = levels.split_at(motive_levels);
                RawExpr::Elim(
                    tr_name(&rec.inductive_name),
                    m.first().cloned().unwrap_or(RawLevel::Zero),
                    rest.to_vec(),
                )
            } else {
                RawExpr::Const(tr_name(name), levels)
            }
        }
        ExprKind::App(f, a) => RawExpr::App(
            Box::new(tr_expr(env, f, lps)?),
            Box::new(tr_expr(env, a, lps)?),
        ),
        ExprKind::Lam(b, ty, body) => RawExpr::Lam(
            tr_binfo(b.info),
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        ),
        ExprKind::Pi(b, ty, body) => RawExpr::Pi(
            tr_binfo(b.info),
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        ),
        ExprKind::Let(_, ty, val, body, _) => RawExpr::Let(
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, val, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        ),
        ExprKind::Lit(Literal::Nat(v)) => RawExpr::Lit(RawLit::Nat(CkBigNat::from_biguint(
            num_bigint::BigUint::parse_bytes(v.to_string().as_bytes(), 10)
                .ok_or_else(|| BridgeError::Unsupported(format!("Nat literal {v}")))?,
        ))),
        ExprKind::Lit(Literal::String(s)) => RawExpr::Lit(RawLit::Str(s.to_string())),
        ExprKind::Proj(s, i, inner) => {
            RawExpr::Proj(tr_name(s), *i, Box::new(tr_expr(env, inner, lps)?))
        }
        ExprKind::MData(_, inner) => tr_expr(env, inner, lps)?,
        other => return Err(BridgeError::Unsupported(format!("{other:?}"))),
    })
}

fn consts_of(e: &Expr, out: &mut BTreeSet<Name>) {
    match e.kind() {
        ExprKind::Const(x, _) => {
            out.insert(x.clone());
        }
        ExprKind::App(f, a) => {
            consts_of(f, out);
            consts_of(a, out);
        }
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            consts_of(t, out);
            consts_of(b, out);
        }
        ExprKind::Let(_, t, v, b, _) => {
            consts_of(t, out);
            consts_of(v, out);
            consts_of(b, out);
        }
        ExprKind::Proj(s, _, inner) => {
            out.insert(s.clone());
            consts_of(inner, out);
        }
        ExprKind::MData(_, inner) => consts_of(inner, out),
        _ => {}
    }
}

/// One unit of admission, in dependency order.
#[derive(Debug, Clone)]
enum Item {
    /// An inductive block, named by its first type.
    Inductive(Name),
    Quot(Name),
    Axiom(Name),
    Def(Name),
}

/// The owner of `x` among the admission units.
fn unit_of(env: &Environment, x: &Name) -> Result<Item, BridgeError> {
    if let Some(c) = env.get_constructor(x) {
        return unit_of(env, &c.inductive_name);
    }
    if let Some(r) = env.get_recursor(x) {
        return unit_of(env, &r.inductive_name);
    }
    if let Some(i) = env.get_inductive(x) {
        return Ok(Item::Inductive(
            i.all_names.first().cloned().unwrap_or_else(|| x.clone()),
        ));
    }
    if let Some(q) = env.get_quot(x) {
        return Ok(if q.kind == QuotKind::Sound {
            Item::Axiom(x.clone())
        } else {
            Item::Quot(x.clone())
        });
    }
    let c = env
        .get_const(x)
        .ok_or_else(|| BridgeError::Missing(x.to_string()))?;
    Ok(match (&c.value, c.kind) {
        (None, _) | (_, ConstantKind::Axiom) => Item::Axiom(x.clone()),
        _ => Item::Def(x.clone()),
    })
}

fn unit_key(i: &Item) -> String {
    match i {
        Item::Inductive(x) => format!("I {x}"),
        Item::Quot(x) => format!("Q {x}"),
        Item::Axiom(x) => format!("A {x}"),
        Item::Def(x) => format!("D {x}"),
    }
}

/// The constants a unit's admission reads.
fn unit_deps(env: &Environment, i: &Item) -> Result<BTreeSet<Name>, BridgeError> {
    let mut out = BTreeSet::new();
    match i {
        Item::Inductive(x) => {
            let d = env
                .inductive_decl_of(x)
                .ok_or_else(|| BridgeError::Missing(x.to_string()))?;
            for t in &d.types {
                consts_of(&t.type_, &mut out);
                for c in &t.constructors {
                    consts_of(&c.type_, &mut out);
                }
            }
        }
        Item::Quot(x) => consts_of(
            &env.get_quot(x)
                .ok_or_else(|| BridgeError::Missing(x.to_string()))?
                .type_,
            &mut out,
        ),
        Item::Axiom(x) => {
            let ty = env
                .get_quot(x)
                .map(|q| q.type_.clone())
                .or_else(|| env.get_const(x).map(|c| c.type_.clone()))
                .ok_or_else(|| BridgeError::Missing(x.to_string()))?;
            consts_of(&ty, &mut out);
        }
        Item::Def(x) => {
            let c = env
                .get_const(x)
                .ok_or_else(|| BridgeError::Missing(x.to_string()))?;
            consts_of(&c.type_, &mut out);
            if let Some(v) = &c.value {
                consts_of(v, &mut out);
            }
        }
    }
    Ok(out)
}

/// The admission units of `roots`' cone, dependencies first (iterative DFS).
fn admission_order(env: &Environment, roots: &[Name]) -> Result<Vec<Item>, BridgeError> {
    let mut order = Vec::new();
    let mut done: HashSet<String> = HashSet::new();
    let mut on_stack: HashSet<String> = HashSet::new();
    for r in roots {
        let root = unit_of(env, r)?;
        let mut stack: Vec<(Item, Vec<Item>)> = Vec::new();
        if done.contains(&unit_key(&root)) {
            continue;
        }
        let deps = unit_deps(env, &root)?
            .iter()
            .map(|d| unit_of(env, d))
            .collect::<Result<Vec<_>, _>>()?;
        on_stack.insert(unit_key(&root));
        stack.push((root, deps));
        while let Some((item, deps)) = stack.last_mut() {
            if let Some(d) = deps.pop() {
                let k = unit_key(&d);
                if done.contains(&k) || on_stack.contains(&k) || k == unit_key(item) {
                    continue;
                }
                let dd = unit_deps(env, &d)?
                    .iter()
                    .map(|x| unit_of(env, x))
                    .collect::<Result<Vec<_>, _>>()?;
                on_stack.insert(k);
                stack.push((d, dd));
            } else {
                let (item, _) = stack.pop().expect("non-empty");
                let k = unit_key(&item);
                on_stack.remove(&k);
                done.insert(k);
                order.push(item);
            }
        }
    }
    Ok(order)
}

fn ck_quot_kind(k: QuotKind) -> CkQuotKind {
    match k {
        QuotKind::Type => CkQuotKind::Type,
        QuotKind::Mk => CkQuotKind::Mk,
        QuotKind::Lift => CkQuotKind::Lift,
        QuotKind::Ind => CkQuotKind::Ind,
        QuotKind::Sound => unreachable!("Quot.sound is admitted as an Ax0 axiom"),
    }
}

/// Ax0's statements, written here from Lean 4's prelude, not read from any
/// `.olean`: an axiom enters ck0 only when its name is one of Ax0 AND its loaded
/// type is definitionally this one (a tampered `propext : False` is refused).
/// `(level params, type)`; binder infos do not matter to definitional equality.
fn ax0_statement(name: &str) -> Option<(u32, RawExpr)> {
    let c = |s: &str, ls: Vec<RawLevel>| RawExpr::Const(CkName::from_dotted(s), ls);
    let app = |f: RawExpr, args: Vec<RawExpr>| {
        args.into_iter()
            .fold(f, |f, a| RawExpr::App(Box::new(f), Box::new(a)))
    };
    let pi = |d: RawExpr, b: RawExpr| RawExpr::Pi(CkBinderInfo::Default, Box::new(d), Box::new(b));
    let bv = RawExpr::BVar;
    let prop = RawExpr::Sort(RawLevel::Zero);
    let u = || RawLevel::Param(0);
    let one = RawLevel::Succ(Box::new(RawLevel::Zero));
    Some(match name {
        // ∀ {a b : Prop}, (a ↔ b) → a = b
        "propext" => (
            0,
            pi(
                prop.clone(),
                pi(
                    prop.clone(),
                    pi(
                        app(c("Iff", vec![]), vec![bv(1), bv(0)]),
                        app(c("Eq", vec![one]), vec![prop, bv(2), bv(1)]),
                    ),
                ),
            ),
        ),
        // ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
        "Quot.sound" => (
            1,
            pi(
                RawExpr::Sort(u()),
                pi(
                    pi(bv(0), pi(bv(1), prop)),
                    pi(
                        bv(1),
                        pi(
                            bv(2),
                            pi(
                                app(bv(2), vec![bv(1), bv(0)]),
                                app(
                                    c("Eq", vec![u()]),
                                    vec![
                                        app(c("Quot", vec![u()]), vec![bv(4), bv(3)]),
                                        app(c("Quot.mk", vec![u()]), vec![bv(4), bv(3), bv(2)]),
                                        app(c("Quot.mk", vec![u()]), vec![bv(4), bv(3), bv(1)]),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
        // {α : Sort u} → Nonempty α → α
        "Classical.choice" => (
            1,
            pi(
                RawExpr::Sort(u()),
                pi(app(c("Nonempty", vec![u()]), vec![bv(0)]), bv(1)),
            ),
        ),
        _ => return None,
    })
}

/// `Ok(())` when `ty` (with `nl` level params) is Ax0's statement of `name`.
fn ax0_statement_matches(ck: &MinimalEnv, name: &str, nl: u32, ty: &Term) -> Result<(), String> {
    let (want_nl, want) = ax0_statement(name).ok_or_else(|| format!("{name} is not in Ax0"))?;
    if nl != want_nl {
        return Err(format!("{name}: {nl} level params, Ax0's has {want_nl}"));
    }
    let want = Term::validate(ck, &want, 0, nl)
        .map_err(|e| format!("{name}: Ax0's statement does not validate here: {e:?}"))?;
    let mut b = Budget::new(CK0_FUEL);
    match clean_ck0::is_def_eq(ck, &want, ty, &mut b) {
        Ok(true) => Ok(()),
        Ok(false) => Err(format!("{name}: the loaded type is not Ax0's statement")),
        Err(e) => Err(format!("{name}: {e:?}")),
    }
}

/// How each unit entered ck0.
#[derive(Default, Debug)]
struct Tally {
    inductive_blocks: usize,
    quot_formers: usize,
    axioms: BTreeSet<String>,
    checked_defs: usize,
    checked_theorems: usize,
}

fn ck_decl(
    env: &Environment,
    boot: &MinimalEnv,
    t: &InductiveType,
    lps: &[Name],
    num_params: u32,
) -> CkIndDecl {
    let nl = u32::try_from(lps.len()).expect("fits");
    let ty = Term::validate(
        boot,
        &tr_expr(env, &t.type_, lps).expect("translate"),
        0,
        nl,
    )
    .unwrap_or_else(|e| panic!("ck0 validates {}'s type: {e:?}", t.name));
    let constructors = t
        .constructors
        .iter()
        .map(|c| CkCtor {
            name: tr_name(&c.name),
            type_: Term::validate(
                boot,
                &tr_expr(env, &c.type_, lps).expect("translate"),
                0,
                nl,
            )
            .unwrap_or_else(|e| panic!("ck0 validates {}'s type: {e:?}", c.name)),
        })
        .collect();
    CkIndDecl {
        name: tr_name(&t.name),
        num_level_params: nl,
        num_params,
        type_: ty,
        constructors,
    }
}

fn admit(env: &Environment, ck: &mut MinimalEnv, item: &Item, tally: &mut Tally) {
    match item {
        Item::Inductive(x) => {
            let d = env.inductive_decl_of(x).expect("present");
            let lps = &d.level_params;
            let nl = u32::try_from(lps.len()).expect("fits");
            // Every type and constructor of the block may name the others.
            let mut boot = ck.clone();
            for t in &d.types {
                boot = boot.with_const(tr_name(&t.name), nl);
                for c in &t.constructors {
                    boot = boot.with_const(tr_name(&c.name), nl);
                }
            }
            let decls: Vec<CkIndDecl> = d
                .types
                .iter()
                .map(|t| ck_decl(env, &boot, t, lps, d.num_params))
                .collect();
            let nested = env.get_inductive(x).is_some_and(|i| i.is_nested);
            if nested {
                assert_eq!(decls.len(), 1, "{x}: a nested block of one type");
                add_inductive_nested(ck, decls.into_iter().next().expect("one"))
                    .unwrap_or_else(|e| panic!("ck0 admits nested inductive {x}: {e:?}"));
            } else if decls.len() == 1 {
                add_inductive(ck, decls.into_iter().next().expect("one"))
                    .unwrap_or_else(|e| panic!("ck0 admits inductive {x}: {e:?}"));
            } else {
                add_inductive_mutual(ck, MutualBlock { decls })
                    .unwrap_or_else(|e| panic!("ck0 admits mutual block {x}: {e:?}"));
            }
            tally.inductive_blocks += 1;
        }
        Item::Quot(x) => {
            let q = env.get_quot(x).expect("present");
            let nl = u32::try_from(q.level_params.len()).expect("fits");
            let ty = Term::validate(
                ck,
                &tr_expr(env, &q.type_, &q.level_params).expect("translate"),
                0,
                nl,
            )
            .unwrap_or_else(|e| panic!("ck0 validates {x}'s type: {e:?}"));
            *ck = std::mem::take(ck)
                .with_const_typed(tr_name(x), nl, ty)
                .with_quot(tr_name(x), nl, ck_quot_kind(q.kind));
            tally.quot_formers += 1;
        }
        Item::Axiom(x) => {
            assert!(
                AX0.contains(&x.to_string().as_str()),
                "ck0 admits an axiom only when it is one of Ax0; {x} is not"
            );
            let (lps, ty) = env
                .get_quot(x)
                .map(|q| (q.level_params.clone(), q.type_.clone()))
                .or_else(|| {
                    env.get_const(x)
                        .map(|c| (c.level_params.clone(), c.type_.clone()))
                })
                .expect("present");
            let nl = u32::try_from(lps.len()).expect("fits");
            let ty = Term::validate(ck, &tr_expr(env, &ty, &lps).expect("translate"), 0, nl)
                .unwrap_or_else(|e| panic!("ck0 validates {x}'s type: {e:?}"));
            let mut b = Budget::new(CK0_FUEL);
            clean_ck0::infer_sort(ck, &ty, &mut b)
                .unwrap_or_else(|e| panic!("{x}'s type is a type: {e:?}"));
            ax0_statement_matches(ck, &x.to_string(), nl, &ty)
                .unwrap_or_else(|e| panic!("ck0 admits an axiom only at Ax0's statement: {e}"));
            *ck = std::mem::take(ck).with_const_typed(tr_name(x), nl, ty);
            tally.axioms.insert(x.to_string());
        }
        Item::Def(x) => {
            let c = env.get_const(x).expect("present");
            let nl = u32::try_from(c.level_params.len()).expect("fits");
            let lps = &c.level_params;
            let ty = Term::validate(
                ck,
                &tr_expr(env, &c.type_, lps).unwrap_or_else(|e| panic!("translate {x}: {e:?}")),
                0,
                nl,
            )
            .unwrap_or_else(|e| panic!("ck0 validates {x}'s type: {e:?}"));
            let value = c.value.as_ref().expect("a definition has a value");
            let val = Term::validate(
                ck,
                &tr_expr(env, value, lps).unwrap_or_else(|e| panic!("translate {x}: {e:?}")),
                0,
                nl,
            )
            .unwrap_or_else(|e| panic!("ck0 validates {x}'s value: {e:?}"));
            let mut b = Budget::new(CK0_FUEL);
            if let Err(e) = clean_ck0::check(ck, &val, &ty, &mut b) {
                panic!("ck0 re-check FAILED for {x}: {e:?}");
            }
            let theorem = c.kind == ConstantKind::Theorem;
            let transparency = if theorem || c.kind == ConstantKind::Opaque {
                Transparency::Opaque
            } else {
                Transparency::Transparent
            };
            *ck = std::mem::take(ck).with_def(tr_name(x), nl, ty, val, transparency);
            if theorem {
                tally.checked_theorems += 1;
            } else {
                tally.checked_defs += 1;
            }
        }
    }
}

/// Why ck0 refused a subject: `check` itself (with its error), or anything else.
#[derive(Debug)]
enum Ck0Refusal {
    Check(clean_ck0::InferError),
    Other(#[expect(dead_code, reason = "read only through Debug, in the failure messages")] String),
}

/// ck0's verdict on `name` (a theorem of `env`) over the admitted `ck`:
/// `Ok(())` when it checks and its inferred type is the declared one.
fn ck0_verdict(env: &Environment, ck: &MinimalEnv, name: &str) -> Result<(), Ck0Refusal> {
    let c = env
        .get_const(&n(name))
        .unwrap_or_else(|| panic!("{name} is loaded"));
    let nl = u32::try_from(c.level_params.len()).expect("fits");
    let ty = Term::validate(
        ck,
        &tr_expr(env, &c.type_, &c.level_params).expect("translate"),
        0,
        nl,
    )
    .map_err(|e| Ck0Refusal::Other(format!("type does not validate: {e:?}")))?;
    let val = Term::validate(
        ck,
        &tr_expr(env, c.value.as_ref().expect("a proof"), &c.level_params).expect("translate"),
        0,
        nl,
    )
    .map_err(|e| Ck0Refusal::Other(format!("value does not validate: {e:?}")))?;
    let mut b = Budget::new(CK0_FUEL);
    clean_ck0::check(ck, &val, &ty, &mut b).map_err(Ck0Refusal::Check)?;
    let mut b = Budget::new(CK0_FUEL);
    let inferred = clean_ck0::infer(ck, &val, &mut b)
        .map_err(|e| Ck0Refusal::Other(format!("infer: {e:?}")))?;
    let mut b = Budget::new(CK0_FUEL);
    if !clean_ck0::is_def_eq(ck, &inferred, &ty, &mut b)
        .map_err(|e| Ck0Refusal::Other(format!("def_eq: {e:?}")))?
    {
        return Err(Ck0Refusal::Other(
            "inferred type is not the declared one".into(),
        ));
    }
    Ok(())
}

#[test]
fn every_existing_member_of_q_rechecks_vf4_and_refuses_the_forgery() {
    let bin = pinned_bin_dir();
    let dir = compiled_fixture_dir(FAMILY);

    // Member 1: Lean 4's kernel.
    for m in ACCEPTED_MODULES {
        let t = Instant::now();
        let (code, err) = leanchecker(&bin, &dir, m);
        assert_eq!(code, Some(0), "leanchecker --fresh {m} must accept: {err}");
        eprintln!(
            "lean-kernel\taccepted\t{m}\t{:.0} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
    }
    let (code, err) = leanchecker(&bin, &dir, FORGED_MODULE);
    assert!(
        code == Some(1) && err.contains("declaration type mismatch") && err.contains(FORGED),
        "leanchecker --fresh {FORGED_MODULE} must refuse {FORGED}: exit {code:?}\n{err}"
    );
    eprintln!("lean-kernel\trefused\t{FORGED}\tdeclaration type mismatch");

    // Member 2: clean-ck0, over what Clean's loader reads from the same bytes.
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned lib");
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(&mut env, "ChkLIAHonest", &[dir.clone(), lib.clone()])
        .unwrap_or_else(|e| panic!("load ChkLIAHonest: {e}"));
    let mut certs: Vec<String> = env
        .constants()
        .map(|c| c.name.to_string())
        .filter(|s| {
            s.strip_prefix("ChkLIAF1.").is_some_and(|t| {
                (t.starts_with("f1_") || t.starts_with("cen_")) && !t.contains('.')
            })
        })
        .collect();
    certs.sort();
    assert!(
        certs.iter().any(|c| c.starts_with("ChkLIAF1.f1_")),
        "the corpus module holds F1 certificates"
    );
    let subjects: Vec<String> = SUBJECTS
        .iter()
        .map(|s| (*s).to_string())
        .chain(certs.iter().cloned())
        .chain([HONEST.to_string()])
        .collect();

    assert!(
        env.constants()
            .all(|c| c.name.last_component().as_deref() != Some(AUX_DEF_COMPONENT)),
        "no loaded constant ends in `{AUX_DEF_COMPONENT}`, so the renaming is injective"
    );
    let roots: Vec<Name> = subjects.iter().map(|s| n(s)).collect();
    let order = admission_order(&env, &roots).unwrap_or_else(|e| panic!("closure: {e:?}"));
    let subject_set: HashSet<String> = subjects.iter().cloned().collect();
    let t = Instant::now();
    let mut ck = MinimalEnv::new();
    let mut tally = Tally::default();
    let mut rechecked_subjects = 0usize;
    for item in &order {
        if let Item::Def(x) = item {
            let s = x.to_string();
            if subject_set.contains(&s) {
                // A subject: ck0's own verdict (and the inferred type compared
                // with the declared one) before it joins the environment.
                let ts = Instant::now();
                ck0_verdict(&env, &ck, &s).unwrap_or_else(|e| panic!("ck0 must accept {s}: {e:?}"));
                eprintln!(
                    "ck0\taccepted\t{s}\t{:.1} ms",
                    ts.elapsed().as_secs_f64() * 1e3
                );
                rechecked_subjects += 1;
            }
        }
        admit(&env, &mut ck, item, &mut tally);
    }
    eprintln!(
        "ck0\tcone\t{} units from EMPTY in {:.0} ms: {} inductive blocks (recursors derived by ck0), {} quotient formers, axioms {:?}, {} definitions and {} theorems each checked",
        order.len(),
        t.elapsed().as_secs_f64() * 1e3,
        tally.inductive_blocks,
        tally.quot_formers,
        tally.axioms,
        tally.checked_defs,
        tally.checked_theorems
    );
    assert!(
        tally.axioms.iter().all(|a| AX0.contains(&a.as_str())),
        "only Ax0 axioms entered ck0: {:?}",
        tally.axioms
    );
    assert_eq!(
        rechecked_subjects,
        subject_set.len(),
        "every subject was re-checked by ck0"
    );

    // The Ax0 statement pin (each admitted axiom's loaded type matched it in
    // `admit`), and its negative controls: a tampered `propext : ∀ a b : Prop,
    // a = b`, and `Classical.choice` at `propext`'s statement, do not match.
    let prop = RawExpr::Sort(RawLevel::Zero);
    let tampered = RawExpr::Pi(
        CkBinderInfo::Default,
        Box::new(prop.clone()),
        Box::new(RawExpr::Pi(
            CkBinderInfo::Default,
            Box::new(prop.clone()),
            Box::new([prop, RawExpr::BVar(1), RawExpr::BVar(0)].into_iter().fold(
                RawExpr::Const(
                    CkName::from_dotted("Eq"),
                    vec![RawLevel::Succ(Box::new(RawLevel::Zero))],
                ),
                |f, a| RawExpr::App(Box::new(f), Box::new(a)),
            )),
        )),
    );
    let tampered = Term::validate(&ck, &tampered, 0, 0).expect("validates");
    let refused = ax0_statement_matches(&ck, "propext", 0, &tampered);
    assert!(
        refused.is_err(),
        "control: a tampered propext must not match Ax0's statement"
    );
    eprintln!("ck0\trefused\ttampered propext\t{}", refused.unwrap_err());
    let propext_ty =
        Term::validate(&ck, &ax0_statement("propext").expect("Ax0").1, 0, 0).expect("validates");
    assert!(
        ax0_statement_matches(&ck, "Classical.choice", 0, &propext_ty).is_err(),
        "control: an Ax0 name at another axiom's statement does not match"
    );

    // The forgery, from its own `.olean` bytes, over the same ck0 environment.
    let mut forged_env = Environment::for_lean_replay();
    match load_module_with_deps(&mut forged_env, FORGED_MODULE, &[dir.clone(), lib]) {
        Ok(_) => {
            let verdict = ck0_verdict(&forged_env, &ck, FORGED);
            assert!(
                matches!(
                    verdict,
                    Err(Ck0Refusal::Check(clean_ck0::InferError::TypeMismatch))
                ),
                "ck0 must refuse {FORGED} as a type mismatch (its statement is false by kernel evaluation), got {verdict:?}"
            );
            eprintln!("ck0\trefused\t{FORGED}\tTypeMismatch");
        }
        Err(e) => panic!(
            "Clean's loader must read {FORGED_MODULE}'s bytes (it checks nothing) so ck0 can judge them: {e}"
        ),
    }
}
