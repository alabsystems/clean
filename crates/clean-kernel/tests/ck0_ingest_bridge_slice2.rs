// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! ck2 INGEST BRIDGE — second slice: a REAL, recursor-USING, universe-
//! polymorphic `clean-kernel` theorem re-checked INDEPENDENTLY by `clean-ck0`
//! with its WHOLE transitive dependency tree auto-ingested.
//!
//! GOAL (ck2 "one kernel, three kingdoms"): show the minimal trust root
//! `clean-ck0` inherits clean's verified corpus — here the genuinely
//! recursor-backed lemma `Eq.symm` — instead of re-proving by hand. Slice 1
//! covered a monomorphic (level-0), recursor-free, hand-wired-deps artifact
//! (`And.symm`). Slice 2 adds the three pieces that slice 1 lacked:
//!
//!  1. UNIVERSE POLYMORPHISM. `Eq.symm : {α : Sort u}{a b : α} → a = b → b = a`
//!     carries a universe param `u`. The translator maps clean's NAMED level
//!     params to ck0's POSITIONAL indices over a per-declaration telescope, so
//!     `Sort u`, the `Eq.{u}` const-levels, and the recursor's level vector all
//!     translate faithfully (slice 1 was `Sort 0` only).
//!
//!  2. RECURSOR / ELIM LOWERING. `Eq.symm`'s proof is
//!     `λ {α}{a}{b} h. @Eq.rec.{0,u} α a (motive) (Eq.refl α a) b h`.
//!     A bare `RawExpr::Const("Eq.rec", …)` is REJECTED by ck0's chokepoint
//!     (recursors must arrive as `Elim` so their level vector is kernel-derived,
//!     never producer-authored). The translator LOWERS the recursor const to
//!     `RawExpr::Elim(I, motive_level, ind_levels)` by splitting clean's recursor
//!     level vector `[motive ; ind…]` — so the ι-rule ck0 uses is its OWN
//!     kernel-derived `Eq.rec`, not a re-axiomatized opaque constant.
//!
//!  3. AUTOMATIC DEPENDENCY-CLOSURE. Given the target `Declaration`, the bridge
//!     computes the transitive set of consts it mentions, classifies each
//!     (inductive / constructor / recursor / def-or-theorem), TOPOLOGICALLY
//!     orders them, and admits each into a FRESH ck0 env: inductives via
//!     `add_inductive` (so ck0 DERIVES + kernel-checks their recursors), defs &
//!     theorems via a real ck0 `check(value : type)`. The closure must be
//!     COMPLETE — a missing dependency surfaces as an explicit `BridgeError`,
//!     never a silent skip or unchecked admission.
//!
//! DISCIPLINE: `clean-ck0/src` is NOT modified; the bridge is untrusted glue ck0
//! re-checks. `clean-kernel/src` is untouched (this is a dev-dep test). The
//! translator is total-or-explicit-`BridgeError`; if ck0 ever accepts a
//! translation that is not faithful to the clean artifact, that is a bug to
//! report, not a pass.

use std::collections::{HashMap, HashSet};

use clean_ck0::rawexpr::{BinderInfo as CkBinderInfo, RawLevel};
use clean_ck0::{
    add_inductive, Budget, Constructor as CkCtor, Env as CkEnv, InductiveDecl as CkIndDecl,
    MinimalEnv, Name as CkName, RawExpr, Term, Transparency,
};
use clean_kernel::{Environment, Expr, ExprKind, Level as KLevel, Name as KName};

// ===========================================================================
// Errors — the translator + closure engine FAIL CLOSED.
// ===========================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum BridgeError {
    /// A clean `ExprKind` variant outside the fragment this slice covers.
    UnsupportedExpr(String),
    /// A clean `Level::Param` not in the enclosing declaration's telescope.
    UnknownLevelParam(String),
    /// A recursor const reference whose parent inductive could not be resolved
    /// (so the `Elim` lowering cannot determine how to split the level vector).
    UnresolvableRecursor(String),
    /// A recursor const reference whose level vector is too short to split into
    /// `[motive ; inductive-levels…]`.
    RecursorLevelArity(String),
    /// Dependency closure: a referenced const is absent from the clean env —
    /// the closure is INCOMPLETE. (Surfaces instead of a silent skip.)
    MissingDependency(String),
}

// ===========================================================================
// Universe-polymorphic level + name translation (extension 1).
// ===========================================================================

/// Map a clean universe-parameter `Name` to its positional index using the
/// declaration's `level_params` list. clean uses NAMED params; ck0 uses
/// POSITIONAL indices — the core representation-gap bridge point.
fn level_param_index(lps: &[KName], name: &KName) -> Option<u32> {
    lps.iter()
        .position(|p| p == name)
        .and_then(|i| u32::try_from(i).ok())
}

/// Translate a clean `Level` to a ck0 `RawLevel` against telescope `lps`.
/// Fail-closed on an unknown param.
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

fn tr_binfo(info: clean_kernel::expr::BinderInfo) -> CkBinderInfo {
    match info {
        clean_kernel::expr::BinderInfo::Default => CkBinderInfo::Default,
        clean_kernel::expr::BinderInfo::Implicit => CkBinderInfo::Implicit,
        clean_kernel::expr::BinderInfo::StrictImplicit => CkBinderInfo::StrictImplicit,
        clean_kernel::expr::BinderInfo::InstImplicit => CkBinderInfo::InstImplicit,
    }
}

fn tr_name(n: &KName) -> CkName {
    CkName::from_dotted(&n.to_string())
}

/// Recursor/eliminator name suffixes (mirrors ck0's chokepoint classification).
fn is_recursor_suffix(last: &str) -> bool {
    matches!(
        last,
        "rec" | "recOn" | "casesOn" | "below" | "ibelow" | "brecOn" | "binductionOn" | "brecOnEq"
    )
}

// ===========================================================================
// The Elim-lowering–aware expression translator (extensions 1 + 2).
//
// Needs the clean `Environment` to resolve a recursor const to its parent
// inductive (so it can split the recursor's level vector into the leading
// motive level(s) and the trailing inductive levels — exactly the shape
// `RawExpr::Elim` wants).
// ===========================================================================

/// How a clean recursor const splits into a ck0 `Elim`: the parent inductive
/// name and how many leading levels are MOTIVE levels (`num_motives`, = 1 for a
/// single inductive). The remaining levels are the inductive's own.
struct RecursorShape {
    inductive: CkName,
    num_motive_levels: usize,
}

/// Resolve a clean recursor const `name` (e.g. `Eq.rec`) to its `Elim` shape.
/// Uses the live clean env: a recursor's `RecursorVal` records its inductive and
/// `num_motives`; the inductive's own `num_level_params` is the rest. Returns
/// `None` if `name` is not a known recursor in this env.
fn recursor_shape(env: &Environment, name: &KName) -> Option<RecursorShape> {
    let rec = env.get_recursor(name)?;
    let ind = env.get_inductive(&rec.inductive_name)?;
    // clean lays a recursor's level params out as [motive… ; inductive…]; the
    // inductive's own params are the trailing `ind.level_params.len()`, and the
    // leading `num_motives` are motive universes. (For a single inductive the
    // motive count is 1 when it large-eliminates and 0 when Prop-only — but
    // clean's `Eq.rec` keeps the `v` slot even at motive-level 0, so we derive
    // the motive-level count from the level-vector length, not large_elim.)
    let total = rec.level_params.len();
    let ind_params = ind.level_params.len();
    let num_motive_levels = total.checked_sub(ind_params)?;
    Some(RecursorShape {
        inductive: tr_name(&rec.inductive_name),
        num_motive_levels,
    })
}

/// Translate a clean `Expr` to a ck0 `RawExpr` against telescope `lps`, lowering
/// recursor consts to `Elim`. Total over the covered fragment; fail-closed else.
fn tr_expr(env: &Environment, e: &Expr, lps: &[KName]) -> Result<RawExpr, BridgeError> {
    match e.kind() {
        ExprKind::BVar(i) => Ok(RawExpr::BVar(*i)),
        ExprKind::Sort(l) => Ok(RawExpr::Sort(tr_level(l, lps)?)),
        ExprKind::Const(name, levels) => {
            let is_rec = name
                .last_component()
                .as_deref()
                .is_some_and(is_recursor_suffix);
            if is_rec {
                // EXTENSION 2: lower the recursor const to `Elim`. We MUST find
                // its parent inductive; if we cannot, fail closed (a recursor we
                // cannot place is never silently treated as an opaque const).
                let shape = recursor_shape(env, name)
                    .ok_or_else(|| BridgeError::UnresolvableRecursor(name.to_string()))?;
                let tr_levels: Result<Vec<RawLevel>, BridgeError> =
                    levels.iter().map(|l| tr_level(l, lps)).collect();
                let tr_levels = tr_levels?;
                if tr_levels.len() < shape.num_motive_levels {
                    return Err(BridgeError::RecursorLevelArity(name.to_string()));
                }
                // clean's single-inductive recursors carry exactly ONE motive
                // universe slot; ck0's `Elim` takes a single motive level + the
                // inductive level vector. Take the FIRST motive slot as the ck0
                // motive level and the trailing levels as the inductive levels.
                // (num_motive_levels is 1 for every single inductive here.)
                let (motive_levels, ind_levels) = tr_levels.split_at(shape.num_motive_levels);
                let motive = motive_levels
                    .first()
                    .cloned()
                    .ok_or_else(|| BridgeError::RecursorLevelArity(name.to_string()))?;
                return Ok(RawExpr::Elim(shape.inductive, motive, ind_levels.to_vec()));
            }
            let lv: Result<Vec<RawLevel>, BridgeError> =
                levels.iter().map(|l| tr_level(l, lps)).collect();
            Ok(RawExpr::Const(tr_name(name), lv?))
        }
        ExprKind::App(f, a) => Ok(RawExpr::App(
            Box::new(tr_expr(env, f, lps)?),
            Box::new(tr_expr(env, a, lps)?),
        )),
        ExprKind::Lam(bd, ty, body) => Ok(RawExpr::Lam(
            tr_binfo(bd.info),
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        )),
        ExprKind::Pi(bd, ty, body) => Ok(RawExpr::Pi(
            tr_binfo(bd.info),
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        )),
        ExprKind::Let(_name, ty, val, body, _nondep) => Ok(RawExpr::Let(
            Box::new(tr_expr(env, ty, lps)?),
            Box::new(tr_expr(env, val, lps)?),
            Box::new(tr_expr(env, body, lps)?),
        )),
        ExprKind::Proj(name, idx, inner) => Ok(RawExpr::Proj(
            tr_name(name),
            *idx,
            Box::new(tr_expr(env, inner, lps)?),
        )),
        other => Err(BridgeError::UnsupportedExpr(format!("{other:?}"))),
    }
}

// ===========================================================================
// EXTENSION 3: automatic transitive dependency-closure.
// ===========================================================================

/// What kind of thing a dependency name resolves to in the clean env.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DepKind {
    /// An inductive type — admitted via ck0 `add_inductive` (derives its rec).
    Inductive,
    /// A constructor — admitted implicitly with its inductive; not standalone.
    Constructor { inductive: KName },
    /// A recursor — derived by ck0 from its inductive; not admitted standalone.
    Recursor { inductive: KName },
    /// A def/theorem with a value — admitted via a real ck0 `check`.
    DefOrTheorem,
}

/// Classify a clean name. `None` ⇒ the name is not present in the env at all
/// (an INCOMPLETE closure — the caller turns this into `MissingDependency`).
fn classify(env: &Environment, name: &KName) -> Option<DepKind> {
    if env.get_inductive(name).is_some() {
        return Some(DepKind::Inductive);
    }
    if let Some(c) = env.get_constructor(name) {
        return Some(DepKind::Constructor {
            inductive: c.inductive_name.clone(),
        });
    }
    if let Some(r) = env.get_recursor(name) {
        return Some(DepKind::Recursor {
            inductive: r.inductive_name.clone(),
        });
    }
    // Plain const (def/theorem/axiom). It must exist as a constant.
    env.get_const(name).map(|_| DepKind::DefOrTheorem)
}

/// Collect every `Const` head name mentioned in a clean `Expr`.
fn collect_consts(e: &Expr, out: &mut HashSet<KName>) {
    match e.kind() {
        ExprKind::Const(n, _) => {
            out.insert(n.clone());
        }
        ExprKind::App(f, a) => {
            collect_consts(f, out);
            collect_consts(a, out);
        }
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            collect_consts(t, out);
            collect_consts(b, out);
        }
        ExprKind::Let(_, t, v, b, _) => {
            collect_consts(t, out);
            collect_consts(v, out);
            collect_consts(b, out);
        }
        ExprKind::Proj(_, _, inner) => collect_consts(inner, out),
        _ => {}
    }
}

/// A dependency we have decided to ADMIT into ck0 (inductive or def/theorem).
/// Constructors and recursors are NOT admitted standalone — they ride in with
/// their inductive (constructor) or are derived by ck0 (recursor); we record
/// the requirement that their inductive be in the closure.
#[derive(Debug, Clone)]
enum AdmitItem {
    Inductive(KName),
    DefOrTheorem(KName),
}

/// Compute the transitive dependency closure of `target` and return it in
/// TOPOLOGICAL (dependencies-first) admission order. Fails CLOSED if any
/// referenced name is not in the clean env (`MissingDependency`).
///
/// A name maps to an [`AdmitItem`] as follows: an inductive is admitted; a
/// constructor/recursor pulls its INDUCTIVE into the closure (and is otherwise
/// not a standalone admission); a def/theorem is admitted after a real check.
/// The recursion descends into the type AND (if present) the value of every
/// def/theorem and the types of inductives + their constructors.
fn dependency_closure(env: &Environment, target: &KName) -> Result<Vec<AdmitItem>, BridgeError> {
    let mut order: Vec<AdmitItem> = Vec::new();
    // visiting: on the recursion stack (cycle guard); done: fully emitted.
    let mut done: HashSet<KName> = HashSet::new();
    let mut visiting: HashSet<KName> = HashSet::new();
    visit(env, target, &mut order, &mut done, &mut visiting)?;
    Ok(order)
}

fn visit(
    env: &Environment,
    name: &KName,
    order: &mut Vec<AdmitItem>,
    done: &mut HashSet<KName>,
    visiting: &mut HashSet<KName>,
) -> Result<(), BridgeError> {
    if done.contains(name) || visiting.contains(name) {
        return Ok(());
    }
    let kind =
        classify(env, name).ok_or_else(|| BridgeError::MissingDependency(name.to_string()))?;
    visiting.insert(name.clone());

    // Resolve the "admission node" for this name (the inductive, for ctors/recs).
    match kind {
        DepKind::Inductive => {
            // Descend into the inductive's type + every constructor's type,
            // collecting their const deps first.
            let decl = env
                .inductive_decl_of(name)
                .ok_or_else(|| BridgeError::MissingDependency(name.to_string()))?;
            let mut deps: HashSet<KName> = HashSet::new();
            for t in &decl.types {
                collect_consts(&t.type_, &mut deps);
                for c in &t.constructors {
                    collect_consts(&c.type_, &mut deps);
                }
            }
            // Don't recurse into the inductive's own family names.
            let family: HashSet<KName> = decl
                .types
                .iter()
                .flat_map(|t| {
                    std::iter::once(t.name.clone())
                        .chain(t.constructors.iter().map(|c| c.name.clone()))
                })
                .collect();
            for d in deps {
                if !family.contains(&d) {
                    visit(env, &d, order, done, visiting)?;
                }
            }
            order.push(AdmitItem::Inductive(name.clone()));
            done.insert(name.clone());
            // Mark constructors as done too (admitted with the inductive).
            for t in &decl.types {
                done.insert(t.name.clone());
                for c in &t.constructors {
                    done.insert(c.name.clone());
                }
            }
        }
        DepKind::Constructor { inductive } | DepKind::Recursor { inductive } => {
            // The standalone name is satisfied by admitting/deriving from its
            // inductive. Recurse into the inductive; mark THIS name done.
            visit(env, &inductive, order, done, visiting)?;
            done.insert(name.clone());
        }
        DepKind::DefOrTheorem => {
            let ci = env
                .get_const(name)
                .ok_or_else(|| BridgeError::MissingDependency(name.to_string()))?;
            let mut deps: HashSet<KName> = HashSet::new();
            collect_consts(&ci.type_, &mut deps);
            if let Some(v) = &ci.value {
                collect_consts(v, &mut deps);
            }
            for d in deps {
                if &d != name {
                    visit(env, &d, order, done, visiting)?;
                }
            }
            order.push(AdmitItem::DefOrTheorem(name.clone()));
            done.insert(name.clone());
        }
    }
    visiting.remove(name);
    Ok(())
}

// ===========================================================================
// Admitting a closure into a fresh ck0 env.
// ===========================================================================

/// Translate + admit a single clean inductive into ck0 via `add_inductive`, so
/// ck0 DERIVES and kernel-checks its recursor. Uses the clean env's stored
/// (post-promotion) `num_params` / `level_params` — exactly the shape ck0
/// re-checks. Returns the admitted inductive's name (for the closure log).
fn admit_inductive(clean_env: &Environment, ck_env: &mut MinimalEnv, name: &KName) -> CkName {
    let decl = clean_env
        .inductive_decl_of(name)
        .expect("inductive present (closure guarantees it)");
    assert_eq!(
        decl.types.len(),
        1,
        "slice 2 covers single (non-mutual) inductives only"
    );
    let it = &decl.types[0];
    let num_lvls = u32::try_from(decl.level_params.len()).expect("level param count fits u32");
    let lps = &decl.level_params;

    // Bootstrap env that knows the names being introduced (the inductive + its
    // constructors), so their translated types validate at the producer→kernel
    // boundary — exactly as slice 1 did for `And`.
    let mut boot = MinimalEnv::new().with_const(tr_name(&it.name), num_lvls);
    for c in &it.constructors {
        boot = boot.with_const(tr_name(&c.name), num_lvls);
    }
    // The inductive + ctor types may reference EARLIER closure decls; chain the
    // already-built ck_env in front by copying its const arities is unnecessary
    // here because `Eq` references no prior decls. For generality we validate
    // against `boot` merged with what ck_env knows via re-declaration would be
    // required; slice 2's targets need only `boot`.

    let ind_ty_raw = tr_expr(clean_env, &it.type_, lps).expect("translate inductive type");
    let ind_ty = Term::validate(&boot, &ind_ty_raw, 0, num_lvls)
        .expect("inductive type validates through ck0 chokepoint");

    let mut ctors = Vec::with_capacity(it.constructors.len());
    for c in &it.constructors {
        let craw = tr_expr(clean_env, &c.type_, lps).expect("translate ctor type");
        let cty = Term::validate(&boot, &craw, 0, num_lvls)
            .expect("ctor type validates through ck0 chokepoint");
        ctors.push(CkCtor {
            name: tr_name(&c.name),
            type_: cty,
        });
    }

    let ind = CkIndDecl {
        name: tr_name(&it.name),
        num_level_params: num_lvls,
        num_params: decl.num_params,
        type_: ind_ty,
        constructors: ctors,
    };
    add_inductive(ck_env, ind)
        .expect("ck0 admits inductive + DERIVES + kernel-checks its recursor");
    tr_name(&it.name)
}

/// The result of admitting the whole closure: the ck0 env plus a human-readable
/// log of what was admitted (for the test record + completeness assertions).
struct Admitted {
    env: MinimalEnv,
    /// Inductives admitted (their ck0 names), each of which derived a recursor.
    inductives: Vec<CkName>,
    /// Def/theorem names admitted via a real ck0 check.
    defs_theorems: Vec<CkName>,
}

/// Build a fresh ck0 env by admitting `closure` (topo order). Every inductive
/// derives + kernel-checks its recursor inside `add_inductive`; every
/// def/theorem is admitted only after a real ck0 `check(value : type)`.
/// The TARGET theorem itself is the last item — we do NOT pre-admit it here; the
/// caller checks it explicitly (the headline re-check).
fn admit_closure_except_target(
    clean_env: &Environment,
    closure: &[AdmitItem],
    target: &KName,
) -> Admitted {
    let mut env = MinimalEnv::new();
    let mut inductives = Vec::new();
    let mut defs_theorems = Vec::new();
    // Track per-name level-arity so def/theorem references validate.
    let mut decl_levels: HashMap<CkName, u32> = HashMap::new();

    for item in closure {
        match item {
            AdmitItem::Inductive(n) => {
                let ckn = admit_inductive(clean_env, &mut env, n);
                let nl = u32::try_from(
                    clean_env
                        .inductive_decl_of(n)
                        .expect("present")
                        .level_params
                        .len(),
                )
                .expect("fits");
                decl_levels.insert(ckn.clone(), nl);
                inductives.push(ckn);
            }
            AdmitItem::DefOrTheorem(n) => {
                if n == target {
                    // Leave the target out — the test checks it explicitly.
                    continue;
                }
                admit_def_or_theorem(clean_env, &mut env, n, &mut decl_levels);
                defs_theorems.push(tr_name(n));
            }
        }
    }
    Admitted {
        env,
        inductives,
        defs_theorems,
    }
}

/// Translate a clean def/theorem, run a REAL ck0 `check(value : type)`, and (if
/// it has a value) register it as a transparent ck0 def so later decls can
/// reference + unfold it. Axioms (no value) would register as opaque consts; the
/// slice-2 targets have none, so we fail closed on a value-less const to avoid a
/// silent unchecked admission.
fn admit_def_or_theorem(
    clean_env: &Environment,
    ck_env: &mut MinimalEnv,
    name: &KName,
    decl_levels: &mut HashMap<CkName, u32>,
) {
    let ci = clean_env
        .get_const(name)
        .expect("present (closure guarantees)");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let lps = &ci.level_params;

    let ty_raw = tr_expr(clean_env, &ci.type_, lps).expect("translate dep type");
    let ty = Term::validate(ck_env, &ty_raw, 0, num_lvls).expect("dep type validates");

    let value = ci
        .value
        .as_ref()
        .expect("slice 2 admits only value-carrying defs/theorems (no opaque deps)");
    let val_raw = tr_expr(clean_env, value, lps).expect("translate dep value");
    let val = Term::validate(ck_env, &val_raw, 0, num_lvls).expect("dep value validates");

    // REAL check: ck0 must accept value : type before admission.
    let mut budget = Budget::default_budget();
    clean_ck0::check(ck_env, &val, &ty, &mut budget)
        .expect("ck0 re-checks dependency value : type before admitting it");

    let ckn = tr_name(name);
    *ck_env =
        std::mem::take(ck_env).with_def(ckn.clone(), num_lvls, ty, val, Transparency::Transparent);
    decl_levels.insert(ckn, num_lvls);
}

// ===========================================================================
// Pull the target out of clean + drive the whole pipeline.
// ===========================================================================

fn clean_env_with_eq() -> Environment {
    let mut env = Environment::new();
    env.init_eq()
        .expect("clean init_eq (admits Eq, Eq.refl, Eq.rec, Eq.symm, …)");
    env
}

/// Run the full slice-2 pipeline for `target_name`: pull the clean artifact,
/// compute its dependency closure, admit the closure into a fresh ck0 env,
/// translate the target's type + proof, and return everything needed to
/// re-check + probe. Panics only on translator/closure invariant violations.
struct Pipeline {
    env: MinimalEnv,
    target_ty: Term,
    target_proof: Term,
    // 2026-07-31: written by `run_pipeline` but never read back — the tests
    // assert over `admitted` (the human-readable log) instead. Kept (not
    // deleted) because it is the pipeline's own record of what the closure
    // computation produced; dropping it would mean a future closure assertion
    // has to re-run `dependency_closure` to see it.
    #[allow(dead_code)]
    closure: Vec<AdmitItem>,
    admitted: AdmittedNames,
}

#[derive(Clone)]
struct AdmittedNames {
    inductives: Vec<CkName>,
    defs_theorems: Vec<CkName>,
}

fn run_pipeline(clean_env: &Environment, target_name: &KName) -> Pipeline {
    let ci = clean_env
        .get_const(target_name)
        .expect("target present in clean env");
    let num_lvls = u32::try_from(ci.level_params.len()).expect("fits");
    let lps = ci.level_params.clone();

    let closure = dependency_closure(clean_env, target_name).expect("closure computes");
    let admitted = admit_closure_except_target(clean_env, &closure, target_name);

    // Translate the target's type + proof against the FINAL env.
    let ty_raw = tr_expr(clean_env, &ci.type_, &lps).expect("translate target type");
    let proof_raw = tr_expr(
        clean_env,
        ci.value.as_ref().expect("target has a proof"),
        &lps,
    )
    .expect("translate target proof");
    let target_ty =
        Term::validate(&admitted.env, &ty_raw, 0, num_lvls).expect("target type validates");
    let target_proof =
        Term::validate(&admitted.env, &proof_raw, 0, num_lvls).expect("target proof validates");

    Pipeline {
        env: admitted.env,
        target_ty,
        target_proof,
        closure,
        admitted: AdmittedNames {
            inductives: admitted.inductives,
            defs_theorems: admitted.defs_theorems,
        },
    }
}

// ===========================================================================
// TESTS
// ===========================================================================

const TARGET: &str = "Eq.symm";

#[test]
fn ck0_independently_rechecks_clean_eq_symm() {
    let clean_env = clean_env_with_eq();

    // (0) clean's OWN kernel accepts Eq.symm (it is a real corpus artifact: the
    // type-checked theorem is in the env with a value).
    let symm = clean_env
        .get_const(&KName::from_string(TARGET))
        .expect("Eq.symm present");
    assert!(
        symm.value.is_some(),
        "Eq.symm is a checked theorem with a proof"
    );
    assert_eq!(
        symm.level_params.len(),
        1,
        "Eq.symm is universe-polymorphic (one level param `u`)"
    );

    let p = run_pipeline(&clean_env, &KName::from_string(TARGET));

    // (1) The closure pulled EXACTLY the needed decls: the `Eq` inductive (which
    // derived `Eq.rec` + admitted `Eq.refl`), and no spurious def/theorem.
    assert_eq!(
        p.admitted.inductives,
        vec![CkName::from_dotted("Eq")],
        "closure admitted exactly the `Eq` inductive"
    );
    assert!(
        p.admitted.defs_theorems.is_empty(),
        "Eq.symm's only dependency is the Eq inductive family; no extra defs"
    );

    // (2) The derived recursor kernel-checked in ck0 (add_inductive only returns
    // Ok after kernel-checking the recursor type + ι-rules). Confirm it exists.
    assert_eq!(
        p.env.num_level_params(&CkName::from_dotted("Eq.rec")),
        Some(2),
        "ck0 derived Eq.rec with [motive ; u] level signature"
    );

    // (3) THE HEADLINE: ck0 decides, on its own, that the proof checks against
    // the type — matching clean's verdict.
    let mut budget = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .expect("ck0 INDEPENDENTLY re-checks clean's Eq.symm: proof : type");

    // Sanity: not a vacuous pass — ck0's inferred type is def-eq to the target.
    let mut b2 = Budget::default_budget();
    let inferred = clean_ck0::infer(&p.env, &p.target_proof, &mut b2).expect("infer proof");
    let mut b3 = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(&p.env, &inferred, &p.target_ty, &mut b3).expect("def_eq"),
        "ck0's inferred type is def-eq to the translated clean type"
    );
}

#[test]
fn ck0_rejects_corrupted_eq_symm_proof() {
    // GENUINENESS #1: tamper the proof so it is no longer a proof of the stated
    // type. We swap the recursor's MINOR premise (`Eq.refl α a`, the base case)
    // for the major-premise hypothesis `h`, breaking the ι-typed witness. ck0
    // must reject with a real type mismatch, not a parse/validate error.
    let clean_env = clean_env_with_eq();
    let target = KName::from_string(TARGET);
    let p = run_pipeline(&clean_env, &target);

    // good proof checks (baseline)
    let mut b0 = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut b0).expect("good proof checks");

    // Corrupt the clean proof, re-run the pipeline's translation on it.
    let ci = clean_env.get_const(&target).expect("present");
    let corrupt = corrupt_recursor_base(ci.value.as_ref().expect("proof"));
    let corrupt_raw = tr_expr(&clean_env, &corrupt, &ci.level_params).expect("tr corrupt");
    let corrupt_proof =
        Term::validate(&p.env, &corrupt_raw, 0, 1).expect("corrupt proof VALIDATES (well-formed)");
    assert_ne!(
        corrupt_proof, p.target_proof,
        "corruption must change the proof term"
    );

    let mut b1 = Budget::default_budget();
    let r = clean_ck0::check(&p.env, &corrupt_proof, &p.target_ty, &mut b1);
    assert!(
        r.is_err(),
        "ck0 must REJECT the corrupted Eq.symm proof: got {r:?}"
    );
}

#[test]
fn ck0_eq_rec_iota_is_faithful_not_axiomatized() {
    // GENUINENESS #2: probe that ck0's lowered `Eq.rec` is the GENUINE
    // kernel-derived eliminator with the right ι-rule — applied to the only
    // constructor `Eq.refl`, it ι-reduces to the minor premise. If `Eq.rec` were
    // a re-axiomatized opaque constant, no such reduction would fire.
    let clean_env = clean_env_with_eq();
    let target = KName::from_string(TARGET);
    let p = run_pipeline(&clean_env, &target);
    let env = &p.env;

    // Build `@Eq.rec.{0,0} α a (motive) base (b:=a) (Eq.refl α a)` over a closed
    // ground inductive so the ι-rule on `Eq.refl` must fire to `base`.
    // Use Nat as the carrier α and a concrete element to keep it closed: but we
    // only have Eq in this env, so build it abstractly under binders instead and
    // probe ι by whnf of the recursor applied to the refl constructor.
    //
    // We lower clean's own `Eq.rec` exactly as the translator does. To get a
    // GROUND major premise we instantiate everything at α := Eq's own carrier is
    // circular; instead build it under a context (α : Sort 0)(a : α) and apply
    // to `Eq.refl α a`, then whnf — the major is a literal constructor app, so
    // the iota rule fires regardless of the open α/a (they are just BVars).
    //
    //   term = λ (α : Sort 0) (a : α).
    //            @Eq.rec α a (λ (x:α)(_:Eq a x). α) a (b:=a) (Eq.refl α a)
    // whnf of the body must be `a` (BVar 0 under the two binders).
    let sort0 = RawExpr::Sort(RawLevel::Zero);
    let alpha = || RawExpr::BVar(1); // under λα λa, α = BVar 1
    let a_var = || RawExpr::BVar(0); // a = BVar 0
    let eq_ind = CkName::from_dotted("Eq");
    // Elim head: motive level 0, inductive level [0].
    let elim = RawExpr::Elim(eq_ind.clone(), RawLevel::Zero, vec![RawLevel::Zero]);
    // motive = λ (x:α)(_:Eq a x). α   (lands in Sort 0 → fine for a Prop-ish probe)
    // de Bruijn: the motive is built INSIDE the `λα λa` frame.
    //   * x's domain `α` is under λα λa            → α = BVar 1
    //   * `Eq a x`'s scope is under λα λa λx        → α=BVar 2, a=BVar 1, x=BVar 0
    //   * the body `α` is under λα λa λx λ_         → α = BVar 3
    let eq_a_x = RawExpr::App(
        Box::new(RawExpr::App(
            Box::new(RawExpr::App(
                Box::new(RawExpr::Const(eq_ind.clone(), vec![RawLevel::Zero])),
                Box::new(RawExpr::BVar(2)), // α
            )),
            Box::new(RawExpr::BVar(1)), // a
        )),
        Box::new(RawExpr::BVar(0)), // x
    );
    let motive = RawExpr::Lam(
        CkBinderInfo::Default,
        Box::new(alpha()), // x : α  (BVar 1 under λα λa)
        Box::new(RawExpr::Lam(
            CkBinderInfo::Default,
            Box::new(eq_a_x),
            Box::new(RawExpr::BVar(3)), // α
        )),
    );
    // base : motive a (refl) — we just use `a` (BVar 0). Its type is `α` = motive output.
    let base = a_var();
    // major = Eq.refl α a
    let refl = RawExpr::App(
        Box::new(RawExpr::App(
            Box::new(RawExpr::Const(
                CkName::from_dotted("Eq.refl"),
                vec![RawLevel::Zero],
            )),
            Box::new(alpha()),
        )),
        Box::new(a_var()),
    );
    // @Eq.rec α a motive base (b := a) (refl)
    let rec_app = apps(elim, vec![alpha(), a_var(), motive, base, a_var(), refl]);
    let body = rec_app;
    let term_raw = RawExpr::Lam(
        CkBinderInfo::Default,
        Box::new(sort0.clone()),
        Box::new(RawExpr::Lam(
            CkBinderInfo::Default,
            Box::new(RawExpr::BVar(0)), // a : α
            Box::new(body),
        )),
    );
    let term = Term::validate_closed(env, &term_raw).expect("iota-probe term validates");

    // Reduce the body under the binders: whnf the full lambda won't enter the
    // body, so we instead build the body as a standalone closed-under-context
    // term and whnf it via infer/def_eq against `a`. Easiest faithful probe:
    // the whole λ is def-eq to `λ (α:Sort 0)(a:α). a` (identity), iff the ι-rule
    // fired (recursor on refl ~> base = a).
    let id_raw = RawExpr::Lam(
        CkBinderInfo::Default,
        Box::new(sort0),
        Box::new(RawExpr::Lam(
            CkBinderInfo::Default,
            Box::new(RawExpr::BVar(0)),
            Box::new(RawExpr::BVar(0)), // a
        )),
    );
    let id_term = Term::validate_closed(env, &id_raw).expect("identity validates");
    let mut budget = Budget::default_budget();
    assert!(
        clean_ck0::is_def_eq(env, &term, &id_term, &mut budget).expect("def_eq runs"),
        "Eq.rec on Eq.refl must ι-reduce to the base case (recursor is the genuine \
         kernel-derived eliminator, not an opaque axiom)"
    );

    // And NOT def-eq to a different function (sanity that the equality is real).
    let const_alpha_raw = RawExpr::Lam(
        CkBinderInfo::Default,
        Box::new(RawExpr::Sort(RawLevel::Zero)),
        Box::new(RawExpr::Lam(
            CkBinderInfo::Default,
            Box::new(RawExpr::BVar(0)),
            Box::new(RawExpr::BVar(1)), // α, not a
        )),
    );
    let const_alpha = Term::validate_closed(env, &const_alpha_raw).expect("validates");
    let mut b2 = Budget::default_budget();
    assert!(
        !clean_ck0::is_def_eq(env, &term, &const_alpha, &mut b2).expect("def_eq"),
        "the ι-reduct is `a`, not `α` — the probe distinguishes the reduct"
    );
}

#[test]
fn dependency_omission_makes_ck0_fail() {
    // DEP-CLOSURE COMPLETENESS: the closure is load-bearing. If we OMIT the `Eq`
    // inductive (the only real dependency), translating the target's recursor
    // reference cannot even resolve its Elim shape against an env that lacks it —
    // and validating the proof against that env FAILS. We show both:
    //   (a) the recursor lowering still produces an Elim (it reads the CLEAN env
    //       for shape), but
    //   (b) validating that Elim against a ck0 env WITHOUT `Eq` is rejected
    //       (ElimRef::mk: the inductive is unknown), i.e. the missing dep surfaces
    //       as a hard ck0 failure, never a silent pass.
    let clean_env = clean_env_with_eq();
    let target = KName::from_string(TARGET);
    let ci = clean_env.get_const(&target).expect("present");

    // Empty ck0 env: `Eq` deliberately NOT admitted.
    let empty = MinimalEnv::new();
    let proof_raw = tr_expr(
        &clean_env,
        ci.value.as_ref().expect("proof"),
        &ci.level_params,
    )
    .expect("tr");
    let r = Term::validate(&empty, &proof_raw, 0, 1);
    assert!(
        r.is_err(),
        "without the `Eq` inductive admitted, ck0 must REJECT the proof (Elim on \
         an unknown inductive): got {r:?}"
    );

    // And confirm the FULL closure (with Eq) DOES make it pass — the dep is what
    // flips the verdict.
    let p = run_pipeline(&clean_env, &target);
    let mut budget = Budget::default_budget();
    clean_ck0::check(&p.env, &p.target_proof, &p.target_ty, &mut budget)
        .expect("with the closure, ck0 accepts — the dep is load-bearing");
}

#[test]
fn translation_is_universe_poly_and_recursor_lowered() {
    // FAITHFULNESS: the translated artifact is the structural image of clean's
    // Eq.symm — universe-polymorphic (Sort with a Param level) and the proof
    // genuinely lowers the recursor to an `Elim` (not a Const, not a stub).
    let clean_env = clean_env_with_eq();
    let target = KName::from_string(TARGET);
    let ci = clean_env.get_const(&target).expect("present");
    let lps = &ci.level_params;

    let ty_raw = tr_expr(&clean_env, &ci.type_, lps).expect("tr type");
    let proof_raw = tr_expr(&clean_env, ci.value.as_ref().expect("proof"), lps).expect("tr proof");

    // Type: ∀ {α:Sort u}{a b:α}, Eq a b → Eq b a → 4 Pis, codomain head `Eq`,
    // and the FIRST binder's domain is `Sort (Param 0)` (universe poly).
    let (npi, head) = count_pis_and_head(&ty_raw);
    assert_eq!(npi, 4, "Eq.symm type has 4 Pi binders");
    assert_eq!(head, Some("Eq".to_string()), "codomain head is `Eq`");
    assert!(
        matches!(
            first_binder_domain(&ty_raw),
            Some(RawExpr::Sort(RawLevel::Param(0)))
        ),
        "first binder is `Sort (Param 0)` — universe-polymorphic translation"
    );

    // Proof: 4 Lam binders; the body head is an `Elim` over `Eq` (recursor
    // lowered), NOT a `Const("Eq.rec", …)`.
    let (nlam, body) = strip_lams(&proof_raw);
    assert_eq!(nlam, 4, "Eq.symm proof has 4 Lam binders");
    let (bhead, _) = unfold_apps_raw(body);
    match bhead {
        RawExpr::Elim(ind, motive, ind_levels) => {
            assert_eq!(*ind, CkName::from_dotted("Eq"), "Elim over `Eq`");
            assert_eq!(
                *motive,
                RawLevel::Zero,
                "motive level is 0 (Eq.symm : Prop)"
            );
            assert_eq!(
                *ind_levels,
                vec![RawLevel::Param(0)],
                "inductive level is the polymorphic `u` (Param 0)"
            );
        }
        other => panic!("proof body head must be a lowered Elim, got {other:?}"),
    }

    // The proof also references the genuine witness `Eq.refl` (the minor premise
    // base case) — not a degenerate stand-in.
    let names = collect_raw_consts(&proof_raw);
    assert!(
        names.contains("Eq.refl"),
        "proof uses the Eq.refl base case"
    );
    // And it must NOT contain a bare `Eq.rec` Const (it was lowered to Elim).
    assert!(
        !names.contains("Eq.rec"),
        "no residual `Eq.rec` Const — the recursor was lowered to Elim"
    );

    // For the record (visible with --nocapture).
    println!("CLEAN Eq.symm TYPE : {:?}", ci.type_.kind());
    println!("ck0   Eq.symm TYPE : {ty_raw:?}");
    println!(
        "CLEAN Eq.symm PROOF: {:?}",
        ci.value.as_ref().unwrap().kind()
    );
    println!("ck0   Eq.symm PROOF: {proof_raw:?}");
}

#[test]
fn closure_completeness_missing_dep_is_explicit_error() {
    // DEP-CLOSURE COMPLETENESS (engine level): a reference to a name absent from
    // the clean env is an EXPLICIT `MissingDependency`, never a silent skip.
    let clean_env = clean_env_with_eq();
    // Forge an expr that references a non-existent const.
    let bogus = Expr::const_(KName::from_string("Does.Not.Exist"), vec![]);
    let mut out = HashSet::new();
    collect_consts(&bogus, &mut out);
    assert!(out.contains(&KName::from_string("Does.Not.Exist")));
    // Closing over a name that is not in the env yields MissingDependency.
    let r = dependency_closure(&clean_env, &KName::from_string("Does.Not.Exist"));
    assert!(
        matches!(&r, Err(BridgeError::MissingDependency(n)) if n == "Does.Not.Exist"),
        "an absent dependency surfaces as an explicit error: got {r:?}"
    );
}

// ===========================================================================
// Corruption: swap the recursor's base (minor) for the major hypothesis.
// ===========================================================================

/// clean's Eq.symm proof body is
///   `@Eq.rec α a motive base b h`  (after stripping the 4 outer lambdas).
/// We rewrite the `base` (5th-from-spine arg = the minor premise `Eq.refl α a`)
/// to `h` (the major hypothesis BVar). The result is well-formed but the minor
/// premise now has the wrong type, so ck0 must reject it.
fn corrupt_recursor_base(value: &Expr) -> Expr {
    // value = λ{α}λ{a}λ{b}λ(h). BODY   (4 lambdas)
    fn rebuild_lams(value: &Expr, depth: u32) -> Expr {
        if let ExprKind::Lam(bd, ty, body) = value.kind() {
            if depth < 4 {
                return Expr::lam(*bd, (**ty).clone(), rebuild_lams(body, depth + 1));
            }
        }
        // at the body: spine `@Eq.rec α a motive base b h`
        corrupt_body(value)
    }
    rebuild_lams(value, 0)
}

/// Replace the `base` argument (4th explicit app arg counting from the head:
/// head=Eq.rec, args = [α, a, motive, base, b, h]) with `h` (the last arg).
fn corrupt_body(body: &Expr) -> Expr {
    let (head, args) = unfold_apps_expr(body);
    assert_eq!(
        args.len(),
        6,
        "Eq.rec applied to 6 args (α a motive base b h)"
    );
    let mut new_args = args.clone();
    // base is index 3; h is index 5. Overwrite base with h.
    new_args[3] = args[5].clone();
    rebuild_apps(head, &new_args)
}

fn unfold_apps_expr(e: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut cur = e.clone();
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = (**f).clone();
    }
    args.reverse();
    (cur, args)
}

fn rebuild_apps(head: Expr, args: &[Expr]) -> Expr {
    let mut cur = head;
    for a in args {
        cur = Expr::app(cur, a.clone());
    }
    cur
}

// ===========================================================================
// Small RawExpr inspectors (test-local).
// ===========================================================================

fn apps(head: RawExpr, args: Vec<RawExpr>) -> RawExpr {
    let mut cur = head;
    for a in args {
        cur = RawExpr::App(Box::new(cur), Box::new(a));
    }
    cur
}

fn count_pis_and_head(e: &RawExpr) -> (u32, Option<String>) {
    let mut n = 0;
    let mut cur = e;
    while let RawExpr::Pi(_, _, codom) = cur {
        n += 1;
        cur = codom;
    }
    (n, raw_head_const(cur))
}

fn first_binder_domain(e: &RawExpr) -> Option<RawExpr> {
    match e {
        RawExpr::Pi(_, dom, _) => Some((**dom).clone()),
        _ => None,
    }
}

fn strip_lams(e: &RawExpr) -> (u32, &RawExpr) {
    let mut n = 0;
    let mut cur = e;
    while let RawExpr::Lam(_, _, body) = cur {
        n += 1;
        cur = body;
    }
    (n, cur)
}

fn unfold_apps_raw(e: &RawExpr) -> (&RawExpr, Vec<&RawExpr>) {
    let mut args = Vec::new();
    let mut cur = e;
    while let RawExpr::App(f, a) = cur {
        args.push(a.as_ref());
        cur = f;
    }
    args.reverse();
    (cur, args)
}

fn raw_head_const(e: &RawExpr) -> Option<String> {
    let (head, _) = unfold_apps_raw(e);
    match head {
        RawExpr::Const(n, _) => Some(format!("{n}")),
        _ => None,
    }
}

fn collect_raw_consts(e: &RawExpr) -> HashSet<String> {
    let mut out = HashSet::new();
    let mut stack = vec![e];
    while let Some(node) = stack.pop() {
        match node {
            RawExpr::Const(n, _) => {
                out.insert(format!("{n}"));
            }
            RawExpr::Elim(n, _, _) => {
                out.insert(format!("{n}.rec(elim)"));
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
