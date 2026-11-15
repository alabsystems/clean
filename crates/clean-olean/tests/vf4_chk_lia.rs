// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VF4 (proven-core plan, increment 5): `chk_LIA`, the linear-integer-arithmetic
//! certificate checker, and `chk_LIA_sound`, admitted through the reference entry
//! with an axiom closure ⊆ Ax0 (`propext`, `Quot.sound`, `Classical.choice`).
//!
//! The checker, its proof and the statement pin are the importable theory
//! `theories/chk_lia/` (a Lake library over `Init` only, R162; its README has the
//! pinned `#print axioms`). The fixture family
//! `tests/fixtures/lean/v4.30.0-rc2/chk_lia/` compiles that theory first (its
//! `ORDER`'s `theory chk_lia` line) and then the negative-control module, with
//! the pinned `lean -o`; this test reads the compiled modules and holds them to
//! the KR0/KR1 fence:
//!
//! * **The closure.** In the loaded environment, `chk_LIA_sound`'s full axiom
//!   closure (`axiom_deps` ⊎ `foundational_axiom_deps`) is ⊆ Ax0. Control: the
//!   same audit names `ChkLIA.planted` for `planted_mut_u8_add_unsat`.
//! * **The entry.** The base is the dependency cone of the subjects, admitted
//!   from EMPTY through the entry (`reference_base_closed`), so every helper lemma
//!   and definition passed the entry's Ax0 and tripwire fences too. Then
//!   `chk_LIA_sound`, each certificate and the corollary are admitted through
//!   `ReferenceKernel::add_checked` under their own names, and the entry's own
//!   environment audits `chk_LIA_sound`'s closure ⊆ Ax0 again.
//! * **Certificates.** Each `cert_*` (`chk_LIA … = true := rfl`) is accepted by
//!   kernel evaluation. Each of the three `mut_*` changes one coefficient of a
//!   certificate's problem: its `= false := rfl` is accepted and the same
//!   statement forged to `= true`, with the same proof, is refused. The `edge_*`
//!   cases pin the checker clauses no certificate reaches (closing on `0 ≤ 0`,
//!   on no constraint, a `d ∈ {0, 1}` step shifting the bound). Every decided
//!   statement is also rebuilt with its own right-hand side and must be ACCEPTED
//!   under a fresh name: the positive control that makes each flipped refusal a
//!   verdict of kernel evaluation, not of a malformed forgery.
//! * **The statement.** `ChkLIASpec.statement_pin` restates `chk_LIA_sound`
//!   verbatim and `spec_sound` restates it over `holds`, a semantics written apart
//!   from `ChkLIA.dot`/`Cons.sat` (`holds_nonvacuous`, `holds_refutes`: neither
//!   `True` nor `False`). Both are admitted through the entry, `chk_LIA_sound`'s
//!   proof is admitted again at `statement_pin`'s type, and this test checks
//!   the shape of both types (`∀ cs cert, chk_LIA cs cert = true → ¬ ∃ ρ, ∀ c ∈
//!   cs, P c ρ`, with `P` `Cons.sat` and `holds` respectively), so a weakened
//!   statement whose proof still cites the lemmas cannot pass.
//! * **Cases.** `chk_LIA_cases` (one certificate per disjunct, R162) and
//!   `chk_LIA_cases_sound` go through the same gates: the closure ⊆ Ax0, its
//!   decided statements admitted, rebuilt and flipped, and its statement pinned
//!   like `chk_LIA_sound`'s: `ChkLIASpec.cases_statement_pin` (verbatim) and
//!   `cases_spec_sound` (over `holds`) are admitted, the theorem's proof is
//!   admitted again at the pin's type, and `cases_shape` checks all three types
//!   node by node (`ps : List (List Cons × List Step)`, `p ∈ ps`, `ρ : Nat →
//!   Int`, `c ∈ p.1` with `p` the bound case, the predicate). Its negative
//!   controls are `ChkLIAPlanted`'s true, Ax0-only, weaker statements
//!   (`weak_cases_padded`: every case padded with `0 ≤ -1`, proved without the
//!   hypothesis; `weak_cases_nat_rho`: `ρ : Nat → Nat`): each fails the shape
//!   check, and its proof at the pin's type is refused as a type mismatch.
//! * **Ax0's negative control.** Declaring `ChkLIA.planted : False` through the
//!   entry is refused with `OutsideAx0`, so nothing resting on it can enter.
//!
//! One test function on purpose: the entry is `&mut` and each step builds on the
//! last. Every module of the family is `prelude`, so the load is the 88 `Init`
//! modules `ChkLIA` imports, not all of `Init`.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{Expr, ExprKind, UsedConstants};
use clean_kernel::name::Name;
use clean_kernel::{KernelEnvError, KernelTypeError, ReferenceKernel, ReferenceRefusal, TheoryId};
use clean_olean::load_module_with_deps;
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::reference_base_closed;
use clean_olean::test_support::compiled_fixture_dir;

const PINNED: &str = "v4.30.0-rc2";
const FAMILY: &str = "chk_lia";
const MODULE: &str = "ChkLIAPlanted";

/// The theory's directory, relative to the workspace root: the test reads its
/// modules from there and nowhere else.
const THEORY_DIR: &str = "theories/chk_lia";
const THEORY_MODULES: [&str; 3] = ["ChkLIA", "ChkLIASpec", "ChkLIACases"];

const SOUND: &str = "ChkLIA.chk_LIA_sound";
/// Soundness of the per-disjunct checker.
const CASES_SOUND: &str = "ChkLIA.chk_LIA_cases_sound";
/// `chk_LIA_cases …` decided by kernel evaluation.
const CASES_DECIDED: [&str; 4] = [
    "ChkLIA.cert_cases_ne",
    "ChkLIA.mut_cases_ne",
    "ChkLIA.edge_cases_refused",
    "ChkLIA.edge_cases_empty",
];
const CERTS: [&str; 4] = [
    "ChkLIA.cert_u8_add",
    "ChkLIA.cert_two_x_eq_one",
    "ChkLIA.cert_index_bound",
    "ChkLIA.cert_cycle64",
];
const MUTANTS: [&str; 3] = [
    "ChkLIA.mut_u8_add",
    "ChkLIA.mut_two_x_eq_one",
    "ChkLIA.mut_index_bound",
];
/// Checker clauses no certificate above distinguishes; each `= true` or `= false`.
const EDGES: [&str; 5] = [
    "ChkLIA.edge_empty",
    "ChkLIA.edge_bound_zero",
    "ChkLIA.edge_d1_no_shift",
    "ChkLIA.edge_d0_no_shift",
    "ChkLIA.edge_d1_two_step",
];
/// `chk_LIA_sound`'s statement, verbatim; cites `chk_LIA_sound`.
const STATEMENT_PIN: &str = "ChkLIASpec.statement_pin";
/// Soundness over the independent semantics `holds`; cites `chk_LIA_sound`.
const SPEC_SOUND: &str = "ChkLIASpec.spec_sound";
/// `chk_LIA_cases_sound`'s statement, verbatim; cites `chk_LIA_cases_sound`.
const CASES_STATEMENT_PIN: &str = "ChkLIASpec.cases_statement_pin";
/// `chk_LIA_cases_sound` over the independent semantics `holds`.
const CASES_SPEC_SOUND: &str = "ChkLIASpec.cases_spec_sound";
/// True, within Ax0, and weaker than the pinned statement (`ChkLIAPlanted`): the
/// shape check must refuse each, and so must the kernel at the pin's type.
const WEAK_CASES: [&str; 2] = ["ChkLIA.weak_cases_padded", "ChkLIA.weak_cases_nat_rho"];
/// `holds` is satisfiable and refutable: it is neither `True` nor `False`.
const SPEC_CONTROLS: [&str; 2] = ["ChkLIASpec.holds_nonvacuous", "ChkLIASpec.holds_refutes"];
/// Cites `chk_LIA_sound` and `cert_u8_add`, so it is admitted after both.
const COROLLARY: &str = "ChkLIA.u8_add_no_overflow";
const PLANTED_AXIOM: &str = "ChkLIA.planted";
const PLANTED_THEOREM: &str = "ChkLIA.planted_mut_u8_add_unsat";
const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];
/// The quotient formers: part of the theory, not axioms (the plan's §2.0), though
/// the closure audit reports them beside the axioms.
const QUOT_FORMERS: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn pinned_lib() -> PathBuf {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this fixture is compiled by {PINNED}; the workspace pin moved"
    );
    let lib = clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (VF4 reads lean-{PINNED})"));
    let toolchain_dir = lib
        .parent()
        .and_then(Path::parent)
        .and_then(Path::file_name)
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    assert!(
        toolchain_dir.ends_with(&format!("---{PINNED}")),
        "the pinned toolchain is not {PINNED} ({toolchain_dir})"
    );
    lib
}

/// The full axiom closure of `name` in `env`: domain axioms and foundational ones.
fn closure(env: &Environment, name: &str) -> BTreeSet<String> {
    let name = n(name);
    let domain = env
        .axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name} is not in the environment"));
    let foundational = env
        .foundational_axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name} is not in the environment"));
    domain
        .into_iter()
        .chain(foundational)
        .map(|a| a.to_string())
        .collect()
}

fn assert_within_ax0(env: &Environment, name: &str, where_: &str) {
    let got = closure(env, name);
    let ax0: BTreeSet<String> = AX0
        .iter()
        .chain(QUOT_FORMERS.iter())
        .map(|s| (*s).to_string())
        .collect();
    assert!(
        got.is_subset(&ax0),
        "{where_}: {name}'s axiom closure {got:?} is not within Ax0 and the quotient formers"
    );
    eprintln!("{where_}: closure({name}) = {got:?} ⊆ Ax0 + quotient formers");
}

/// The loaded theorem `name`, as a fresh declaration under `as_name` with type `type_`.
fn theorem(env: &Environment, name: &str, as_name: &str, type_: Option<Expr>) -> Declaration {
    let c = env
        .get_const(&n(name))
        .unwrap_or_else(|| panic!("{name} is declared by the fixture"));
    Declaration::Theorem {
        name: n(as_name),
        level_params: c.level_params.clone(),
        type_: type_.unwrap_or_else(|| c.type_.clone()),
        value: c
            .value
            .clone()
            .unwrap_or_else(|| panic!("{name} is a theorem with a proof")),
    }
}

/// `@Eq Bool lhs b` rebuilt from `@Eq Bool lhs rhs` with `rhs := b`.
fn with_rhs(env: &Environment, name: &str, b: &str) -> Expr {
    let ty = &env.get_const(&n(name)).expect("declared").type_;
    let args: Vec<Expr> = ty.get_app_args().into_iter().cloned().collect();
    assert_eq!(args.len(), 3, "{name}: `@Eq Bool (chk_LIA …) b`");
    Expr::apps(
        ty.get_app_fn().clone(),
        [args[0].clone(), args[1].clone(), Expr::const_(n(b), vec![])],
    )
}

/// The `Bool` constant a decided statement `@Eq Bool (chk_LIA …) b` names as `b`.
fn decided_rhs(env: &Environment, name: &str) -> &'static str {
    let ty = &env.get_const(&n(name)).expect("declared").type_;
    assert_eq!(head(ty).as_deref(), Some("Eq"), "{name}: `@Eq Bool …`");
    let args: Vec<&Expr> = ty.get_app_args().into_iter().collect();
    assert_eq!(
        head(args[0]).as_deref(),
        Some("Bool"),
        "{name}: over `Bool`"
    );
    assert!(
        matches!(
            head(args[1]).as_deref(),
            Some("ChkLIA.chk_LIA" | "ChkLIA.chk_LIA_cases")
        ),
        "{name}: decides `chk_LIA` or `chk_LIA_cases`"
    );
    match head(args[2]).as_deref() {
        Some("Bool.true") => "Bool.true",
        Some("Bool.false") => "Bool.false",
        other => panic!("{name}: the right-hand side is a `Bool` constant, got {other:?}"),
    }
}

/// The workspace root (two levels above this crate's manifest).
fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("the workspace root")
        .to_path_buf()
}

/// The theory's modules come from `theories/chk_lia`, not from the fixture
/// family: each source is in the theory, none is in the family, and the compiled
/// family directory holds each module's source byte for byte as the theory has it.
fn assert_modules_come_from_the_theory(compiled: &Path) {
    let theory = workspace_root().join(THEORY_DIR);
    let family = clean_olean::test_support::fixture_root().join(FAMILY);
    for m in THEORY_MODULES {
        let source = theory.join(format!("{m}.lean"));
        let bytes = std::fs::read(&source)
            .unwrap_or_else(|e| panic!("the theory holds {}: {e}", source.display()));
        assert!(
            !family.join(format!("{m}.lean")).exists(),
            "{m}.lean must live in {THEORY_DIR} only, not in the fixture family"
        );
        assert_eq!(
            std::fs::read(compiled.join(format!("{m}.lean")))
                .ok()
                .as_deref(),
            Some(bytes.as_slice()),
            "the compiled family's {m}.lean is the theory's"
        );
        assert!(
            compiled.join(format!("{m}.olean")).is_file(),
            "{m}.olean compiled"
        );
    }
    let lake = std::fs::read_to_string(theory.join("lakefile.toml")).expect("lakefile.toml");
    for m in THEORY_MODULES {
        assert!(
            lake.contains(&format!("\"{m}\"")),
            "lakefile.toml's library lists {m}"
        );
    }
    assert_eq!(
        std::fs::read_to_string(theory.join("lean-toolchain"))
            .expect("the theory pins its toolchain")
            .trim(),
        include_str!("../../../lean-toolchain").trim(),
        "the theory's lean-toolchain is the workspace pin"
    );
}

/// The constant at the head of `e`'s application spine.
fn head(e: &Expr) -> Option<String> {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn is_bvar(e: &Expr, i: u32) -> bool {
    matches!(e.kind(), ExprKind::BVar(j) if *j == i)
}

/// `(x : dom) → body` (or `fun`), split; panics on any other node.
fn binder<'a>(e: &'a Expr, lam: bool, what: &str) -> (&'a Expr, &'a Expr) {
    match (e.kind(), lam) {
        (ExprKind::Pi(_, dom, body), false) | (ExprKind::Lam(_, dom, body), true) => (dom, body),
        _ => panic!(
            "{what}: expected a {}, got {e}",
            if lam { "λ" } else { "Π" }
        ),
    }
}

/// The type `∀ (cs : List ChkLIA.Cons) (cert : List ChkLIA.Step), @Eq Bool
/// (chk_LIA cs cert) true → ¬ ∃ ρ : Nat → Int, ∀ c, c ∈ cs → P c ρ`, node by node;
/// `pred` checks `P c ρ` with `c` at de Bruijn index 1 and `ρ` at 2.
fn assert_soundness_shape(env: &Environment, name: &str, pred: impl Fn(&Expr) -> bool) {
    let ty = &env.get_const(&n(name)).expect("declared").type_;
    let (cs_ty, rest) = binder(ty, false, name);
    assert!(
        head(cs_ty).as_deref() == Some("List")
            && cs_ty
                .get_app_args()
                .into_iter()
                .any(|a| head(a).as_deref() == Some("ChkLIA.Cons")),
        "{name}: `cs : List Cons`, got {cs_ty}"
    );
    let (cert_ty, rest) = binder(rest, false, name);
    assert!(
        head(cert_ty).as_deref() == Some("List")
            && cert_ty
                .get_app_args()
                .into_iter()
                .any(|a| head(a).as_deref() == Some("ChkLIA.Step")),
        "{name}: `cert : List Step`, got {cert_ty}"
    );
    let (hyp, concl) = binder(rest, false, name);
    let hyp_args: Vec<&Expr> = hyp.get_app_args().into_iter().collect();
    let call_args: Vec<&Expr> = hyp_args
        .get(1)
        .map(|c| c.get_app_args().into_iter().collect())
        .unwrap_or_default();
    assert!(
        head(hyp).as_deref() == Some("Eq")
            && hyp_args.len() == 3
            && head(hyp_args[1]).as_deref() == Some("ChkLIA.chk_LIA")
            && call_args.len() == 2
            && is_bvar(call_args[0], 1)
            && is_bvar(call_args[1], 0)
            && head(hyp_args[2]).as_deref() == Some("Bool.true"),
        "{name}: the hypothesis is `chk_LIA cs cert = true`, got {hyp}"
    );
    let not_args: Vec<&Expr> = concl.get_app_args().into_iter().collect();
    assert!(
        head(concl).as_deref() == Some("Not") && not_args.len() == 1,
        "{name}: the conclusion is a negation, got {concl}"
    );
    let ex = not_args[0];
    let ex_args: Vec<&Expr> = ex.get_app_args().into_iter().collect();
    assert!(
        head(ex).as_deref() == Some("Exists") && ex_args.len() == 2,
        "{name}: `¬ ∃ ρ, …`, got {ex}"
    );
    let (rho_ty, body) = binder(ex_args[1], true, name);
    let (rho_dom, rho_cod) = binder(rho_ty, false, name);
    assert!(
        head(rho_dom).as_deref() == Some("Nat") && head(rho_cod).as_deref() == Some("Int"),
        "{name}: `ρ : Nat → Int`, got {rho_ty}"
    );
    // Under λ ρ: ρ = #0, h = #1, cert = #2, cs = #3.
    let (c_ty, body) = binder(body, false, name);
    assert_eq!(
        head(c_ty).as_deref(),
        Some("ChkLIA.Cons"),
        "{name}: `∀ c : Cons`"
    );
    // Under Π c: c = #0, cs = #4.
    let (mem, body) = binder(body, false, name);
    let mem_args: Vec<&Expr> = mem.get_app_args().into_iter().collect();
    assert!(
        head(mem).as_deref() == Some("Membership.mem")
            && mem_args.iter().any(|a| is_bvar(a, 4))
            && mem_args.iter().any(|a| is_bvar(a, 0)),
        "{name}: `c ∈ cs`, got {mem}"
    );
    // Under the membership binder: c = #1, ρ = #2.
    assert!(
        pred(body),
        "{name}: the predicate over `c` and `ρ`, got {body}"
    );
    eprintln!("shape	{name}	∀ cs cert, chk_LIA cs cert = true → ¬ ∃ ρ, ∀ c ∈ cs, {body}");
}

/// `List elem` with `elem` the constant `elem_head` (no arguments).
fn is_list_of(e: &Expr, elem_head: &str) -> bool {
    let args: Vec<&Expr> = e.get_app_args().into_iter().collect();
    head(e).as_deref() == Some("List")
        && args.len() == 1
        && head(args[0]).as_deref() == Some(elem_head)
        && args[0].get_app_args().is_empty()
}

/// `List ChkLIA.Cons × List ChkLIA.Step`, the type of one case.
fn is_case_ty(e: &Expr) -> bool {
    let args: Vec<&Expr> = e.get_app_args().into_iter().collect();
    head(e).as_deref() == Some("Prod")
        && args.len() == 2
        && is_list_of(args[0], "ChkLIA.Cons")
        && is_list_of(args[1], "ChkLIA.Step")
}

/// `x ∈ coll`: `@Membership.mem α γ inst coll x` with `coll` and `x` checked by
/// the two predicates, and nothing else bound in the instance arguments.
fn is_mem(e: &Expr, coll: impl Fn(&Expr) -> bool, x: impl Fn(&Expr) -> bool) -> bool {
    let args: Vec<&Expr> = e.get_app_args().into_iter().collect();
    head(e).as_deref() == Some("Membership.mem")
        && args.len() == 5
        && coll(args[3])
        && x(args[4])
        && args[..3].iter().all(|a| !a.has_loose_bvars())
}

/// The type `∀ (ps : List (List Cons × List Step)), chk_LIA_cases ps = true → ∀
/// p, p ∈ ps → ¬ ∃ ρ : Nat → Int, ∀ c : Cons, c ∈ p.1 → P c ρ`, node by node;
/// `pred` checks `P c ρ` with `c` at de Bruijn index 1 and `ρ` at 2. `Err` names
/// the first node that differs (the negative controls in `ChkLIAPlanted` rely on
/// it: a padded case list, a narrower `ρ`).
fn cases_shape(
    env: &Environment,
    name: &str,
    pred: impl Fn(&Expr) -> bool,
) -> Result<String, String> {
    let ty = &env
        .get_const(&n(name))
        .ok_or_else(|| format!("{name}: not declared"))?
        .type_;
    let pi = |e: &Expr, what: &str| match e.kind() {
        ExprKind::Pi(_, dom, body) => Ok((dom.clone(), body.clone())),
        _ => Err(format!("{name}: expected Π at {what}, got {e}")),
    };
    let lam = |e: &Expr, what: &str| match e.kind() {
        ExprKind::Lam(_, dom, body) => Ok((dom.clone(), body.clone())),
        _ => Err(format!("{name}: expected λ at {what}, got {e}")),
    };
    let ensure = |ok: bool, what: String| if ok { Ok(()) } else { Err(what) };
    let (ps_ty, rest) = pi(ty, "ps")?;
    let ps_args: Vec<&Expr> = ps_ty.get_app_args().into_iter().collect();
    ensure(
        head(&ps_ty).as_deref() == Some("List") && ps_args.len() == 1 && is_case_ty(ps_args[0]),
        format!("{name}: `ps : List (List Cons × List Step)`, got {ps_ty}"),
    )?;
    let (hyp, rest) = pi(&rest, "h")?;
    let hyp_args: Vec<&Expr> = hyp.get_app_args().into_iter().collect();
    ensure(
        head(&hyp).as_deref() == Some("Eq")
            && hyp_args.len() == 3
            && head(hyp_args[0]).as_deref() == Some("Bool")
            && head(hyp_args[1]).as_deref() == Some("ChkLIA.chk_LIA_cases")
            && {
                let call: Vec<&Expr> = hyp_args[1].get_app_args().into_iter().collect();
                call.len() == 1 && is_bvar(call[0], 0)
            }
            && head(hyp_args[2]).as_deref() == Some("Bool.true"),
        format!("{name}: the hypothesis is `chk_LIA_cases ps = true`, got {hyp}"),
    )?;
    // Under h: ps = #1.
    let (p_ty, rest) = pi(&rest, "p")?;
    ensure(
        is_case_ty(&p_ty),
        format!("{name}: `p : List Cons × List Step`, got {p_ty}"),
    )?;
    // Under p: p = #0, ps = #2.
    let (hp, concl) = pi(&rest, "p ∈ ps")?;
    ensure(
        is_mem(&hp, |a| is_bvar(a, 2), |a| is_bvar(a, 0)),
        format!("{name}: `p ∈ ps`, got {hp}"),
    )?;
    let not_args: Vec<&Expr> = concl.get_app_args().into_iter().collect();
    ensure(
        head(&concl).as_deref() == Some("Not") && not_args.len() == 1,
        format!("{name}: the conclusion is a negation, got {concl}"),
    )?;
    let ex_args: Vec<&Expr> = not_args[0].get_app_args().into_iter().collect();
    ensure(
        head(not_args[0]).as_deref() == Some("Exists") && ex_args.len() == 2,
        format!("{name}: `¬ ∃ ρ, …`, got {}", not_args[0]),
    )?;
    let (rho_ty, body) = lam(ex_args[1], "ρ")?;
    let (rho_dom, rho_cod) = pi(&rho_ty, "ρ's type")?;
    ensure(
        *ex_args[0] == *rho_ty,
        format!("{name}: `Exists` ranges over ρ's type, got {}", ex_args[0]),
    )?;
    ensure(
        head(&rho_dom).as_deref() == Some("Nat")
            && rho_dom.get_app_args().is_empty()
            && head(&rho_cod).as_deref() == Some("Int")
            && rho_cod.get_app_args().is_empty(),
        format!("{name}: `ρ : Nat → Int`, got {rho_ty}"),
    )?;
    // Under λ ρ: ρ = #0, hp = #1, p = #2.
    let (c_ty, body) = pi(&body, "c")?;
    ensure(
        head(&c_ty).as_deref() == Some("ChkLIA.Cons") && c_ty.get_app_args().is_empty(),
        format!("{name}: `∀ c : Cons`, got {c_ty}"),
    )?;
    // Under Π c: c = #0, p = #3. The collection is exactly `p.1`.
    let (mem, body) = pi(&body, "c ∈ p.1")?;
    let is_p_fst = |a: &Expr| {
        let args: Vec<&Expr> = a.get_app_args().into_iter().collect();
        head(a).as_deref() == Some("Prod.fst")
            && args.len() == 3
            && is_list_of(args[0], "ChkLIA.Cons")
            && is_list_of(args[1], "ChkLIA.Step")
            && is_bvar(args[2], 3)
    };
    ensure(
        is_mem(&mem, is_p_fst, |a| is_bvar(a, 0)),
        format!("{name}: `c ∈ p.1`, got {mem}"),
    )?;
    // Under the membership binder: c = #1, ρ = #2.
    ensure(
        pred(&body),
        format!("{name}: the predicate over `c` and `ρ`, got {body}"),
    )?;
    Ok(format!(
        "∀ ps, chk_LIA_cases ps = true → ∀ p ∈ ps, ¬ ∃ ρ : Nat → Int, ∀ c ∈ p.1, {body}"
    ))
}

fn admit(k: &mut ReferenceKernel, d: Declaration, what: &str) {
    let t = Instant::now();
    let token = k
        .add_checked(d)
        .unwrap_or_else(|e| panic!("{what} must be accepted through the entry: {e}"));
    let ms = t.elapsed().as_secs_f64() * 1e3;
    assert_eq!(token.theory_id(), TheoryId::LeanReferenceV1, "{what}");
    eprintln!("accepted\t{what}\t{ms:.2} ms");
}

#[test]
fn chk_lia_sound_is_admitted_through_the_entry_within_ax0() {
    let lib = pinned_lib();
    let t = Instant::now();
    let compiled = compiled_fixture_dir(FAMILY);
    assert_modules_come_from_the_theory(&compiled);
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(&mut env, MODULE, &[compiled, lib])
        .unwrap_or_else(|e| panic!("load {MODULE}: {e}"));
    eprintln!("load: {:.0} ms", t.elapsed().as_secs_f64() * 1e3);

    // The closure in the loaded environment, and its control.
    assert_within_ax0(&env, SOUND, "loaded");
    assert_within_ax0(&env, COROLLARY, "loaded");
    assert_within_ax0(&env, CASES_SOUND, "loaded");
    let planted = closure(&env, PLANTED_THEOREM);
    assert!(
        planted.contains(PLANTED_AXIOM),
        "control: the audit must name {PLANTED_AXIOM} for {PLANTED_THEOREM}, got {planted:?}"
    );

    // The base: the subjects' cone, minus the subjects, admitted through the entry.
    let subjects: Vec<&str> = std::iter::once(SOUND)
        .chain(CERTS)
        .chain(MUTANTS)
        .chain(EDGES)
        .chain([
            COROLLARY,
            STATEMENT_PIN,
            SPEC_SOUND,
            CASES_SOUND,
            CASES_STATEMENT_PIN,
            CASES_SPEC_SOUND,
        ])
        .chain(SPEC_CONTROLS)
        .chain(CASES_DECIDED)
        .collect();
    let subject_names: HashSet<Name> = subjects.iter().map(|s| n(s)).collect();
    let mut used = HashSet::new();
    for s in &subjects {
        let c = env
            .get_const(&n(s))
            .unwrap_or_else(|| panic!("{s} missing"));
        c.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
        c.value
            .as_ref()
            .unwrap_or_else(|| panic!("{s} has a proof"))
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
    }
    // The weak controls are admitted only at the pin's type (and refused), so
    // their dependencies join the base too.
    for w in WEAK_CASES {
        let c = env
            .get_const(&n(w))
            .unwrap_or_else(|| panic!("{w} missing"));
        c.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
        c.value
            .as_ref()
            .unwrap_or_else(|| panic!("{w} has a proof"))
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
    }
    let weak_names: HashSet<Name> = WEAK_CASES.iter().map(|s| n(s)).collect();
    let targets: BTreeSet<Name> = used
        .into_iter()
        .filter(|x| !subject_names.contains(x) && !weak_names.contains(x))
        .collect();
    assert!(
        targets.contains(&n("ChkLIA.chk_LIA")) && targets.contains(&n("ChkLIA.run_unsat")),
        "the base cone holds the checker and its lemmas"
    );
    let t = Instant::now();
    let built = reference_base_closed(&env, &targets, &ClosedRecheckOptions::default())
        .expect("the reference base starts");
    assert!(
        built.report.passed() && built.entry_refusals.is_empty(),
        "{}\n{:?}",
        built.report.verdict_sentence(),
        built.entry_refusals
    );
    eprintln!(
        "base: {} targets, {} admitted through the entry in {:.0} ms",
        targets.len(),
        built.admitted.len(),
        t.elapsed().as_secs_f64() * 1e3
    );
    assert!(built.admitted.contains(&n("ChkLIA.chk_LIA")));
    let built_has_sound = built.admitted.contains(&n(SOUND));
    assert!(
        built_has_sound == targets.contains(&n("ChkLIA.chk_LIA_cases_sound._f")),
        "{SOUND} is in the base exactly when `chk_LIA_cases_sound._f` (which cites it) is"
    );
    let mut k = built.into_kernel().expect("a passing base");

    // The theorem, then every certificate, then the corollary that uses both.
    // `chk_LIA_cases_sound`'s structural-recursion auxiliary `._f` cites
    // `chk_LIA_sound`, so the base (the subjects' cone) already admitted it
    // through the entry; its proof is then admitted again under a fresh name.
    if built_has_sound {
        admit(
            &mut k,
            theorem(&env, SOUND, "ChkLIA.chk_LIA_sound.reentry", None),
            "ChkLIA.chk_LIA_sound (again, under a fresh name)",
        );
    } else {
        admit(&mut k, theorem(&env, SOUND, SOUND, None), SOUND);
    }
    assert_within_ax0(k.environment(), SOUND, "entry");
    for c in CERTS {
        admit(&mut k, theorem(&env, c, c, None), c);
    }
    admit(&mut k, theorem(&env, COROLLARY, COROLLARY, None), COROLLARY);
    assert_within_ax0(k.environment(), COROLLARY, "entry");
    admit(
        &mut k,
        theorem(&env, CASES_SOUND, CASES_SOUND, None),
        CASES_SOUND,
    );
    assert_within_ax0(k.environment(), CASES_SOUND, "entry");

    // The cases statement: pinned verbatim and over `holds`, each admitted; the
    // theorem's proof admitted again at the pin's type; all three types checked
    // node by node. The weak controls fail the shape check and, at the pin's
    // type, the kernel.
    for s in [CASES_STATEMENT_PIN, CASES_SPEC_SOUND] {
        admit(&mut k, theorem(&env, s, s, None), s);
        assert_within_ax0(k.environment(), s, "entry");
    }
    let cases_pin_ty = env
        .get_const(&n(CASES_STATEMENT_PIN))
        .expect("declared")
        .type_
        .clone();
    admit(
        &mut k,
        theorem(
            &env,
            CASES_SOUND,
            "ChkLIA.chk_LIA_cases_sound.at_pin",
            Some(cases_pin_ty.clone()),
        ),
        "chk_LIA_cases_sound's proof at cases_statement_pin's type",
    );
    let sat_c_rho = |e: &Expr| {
        let args: Vec<&Expr> = e.get_app_args().into_iter().collect();
        head(e).as_deref() == Some("ChkLIA.Cons.sat")
            && args.len() == 2
            && is_bvar(args[0], 1)
            && is_bvar(args[1], 2)
    };
    let holds_c_rho = |e: &Expr| {
        let args: Vec<&Expr> = e.get_app_args().into_iter().collect();
        let field = |a: &Expr, f: &str| {
            let fa: Vec<&Expr> = a.get_app_args().into_iter().collect();
            head(a).as_deref() == Some(f) && fa.len() == 1 && is_bvar(fa[0], 1)
        };
        head(e).as_deref() == Some("ChkLIASpec.holds")
            && args.len() == 3
            && field(args[0], "ChkLIA.Cons.coeffs")
            && field(args[1], "ChkLIA.Cons.bound")
            && is_bvar(args[2], 2)
    };
    for (s, holds) in [
        (CASES_SOUND, false),
        (CASES_STATEMENT_PIN, false),
        (CASES_SPEC_SOUND, true),
    ] {
        let got = if holds {
            cases_shape(&env, s, holds_c_rho)
        } else {
            cases_shape(&env, s, sat_c_rho)
        };
        let got = got.unwrap_or_else(|e| panic!("{e}"));
        eprintln!("shape\t{s}\t{got}");
    }
    for w in WEAK_CASES {
        assert_within_ax0(&env, w, "loaded");
        let refusal = cases_shape(&env, w, sat_c_rho)
            .expect_err("a weakened cases statement must fail the shape check");
        eprintln!("shape refused\t{w}\t{refusal}");
        let at_pin = k.add_checked(theorem(
            &env,
            w,
            &format!("{w}.at_pin"),
            Some(cases_pin_ty.clone()),
        ));
        assert!(
            matches!(
                &at_pin,
                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                }))
            ),
            "{w}'s proof at cases_statement_pin's type must be refused as a type mismatch, got {at_pin:?}"
        );
        eprintln!("refused\t{w}.at_pin\ttype mismatch");
    }

    // The statement: pinned verbatim and over the independent semantics, each
    // admitted through the entry, each type checked node by node here.
    admit(
        &mut k,
        theorem(&env, STATEMENT_PIN, STATEMENT_PIN, None),
        STATEMENT_PIN,
    );
    admit(
        &mut k,
        theorem(&env, SPEC_SOUND, SPEC_SOUND, None),
        SPEC_SOUND,
    );
    assert_within_ax0(k.environment(), SPEC_SOUND, "entry");
    for c in SPEC_CONTROLS {
        admit(&mut k, theorem(&env, c, c, None), c);
    }
    let pinned_ty = env
        .get_const(&n(STATEMENT_PIN))
        .expect("declared")
        .type_
        .clone();
    admit(
        &mut k,
        theorem(&env, SOUND, "ChkLIA.chk_LIA_sound.at_pin", Some(pinned_ty)),
        "chk_LIA_sound's proof at statement_pin's type",
    );
    let pred_over = |p: &'static str, field_args: bool| {
        move |e: &Expr| {
            let args: Vec<&Expr> = e.get_app_args().into_iter().collect();
            let field = |a: &Expr, f: &str| {
                head(a).as_deref() == Some(f)
                    && a.get_app_args()
                        .into_iter()
                        .next_back()
                        .is_some_and(|x| is_bvar(x, 1))
            };
            head(e).as_deref() == Some(p)
                && if field_args {
                    // `holds c.coeffs c.bound ρ`
                    args.len() == 3
                        && field(args[0], "ChkLIA.Cons.coeffs")
                        && field(args[1], "ChkLIA.Cons.bound")
                        && is_bvar(args[2], 2)
                } else {
                    // `Cons.sat c ρ`
                    args.len() == 2 && is_bvar(args[0], 1) && is_bvar(args[1], 2)
                }
        }
    };
    assert_soundness_shape(&env, SOUND, pred_over("ChkLIA.Cons.sat", false));
    assert_soundness_shape(&env, STATEMENT_PIN, pred_over("ChkLIA.Cons.sat", false));
    assert_soundness_shape(&env, SPEC_SOUND, pred_over("ChkLIASpec.holds", true));

    // Every decided statement: three certificates with one changed coefficient
    // (the checker refuses each: `= false` is a theorem), the edge cases, and the
    // accepted certificates. Each is admitted as stated; rebuilt with its own
    // right-hand side under a fresh name it is accepted again (the positive
    // control: the rebuilt statement is well formed, so a refusal of the flip is
    // the kernel evaluating `chk_LIA`); flipped, with the same proof, refused.
    for d in CERTS
        .into_iter()
        .chain(MUTANTS)
        .chain(EDGES)
        .chain(CASES_DECIDED)
    {
        let rhs = decided_rhs(&env, d);
        if MUTANTS.contains(&d) || d == "ChkLIA.mut_cases_ne" {
            assert_eq!(rhs, "Bool.false", "{d}: the checker refuses each mutant");
        }
        if d == "ChkLIA.cert_cases_ne" {
            assert_eq!(rhs, "Bool.true", "{d}: both cases' certificates close");
        }
        if CERTS.contains(&d) {
            assert_eq!(
                rhs, "Bool.true",
                "{d}: the checker accepts each certificate"
            );
        } else {
            admit(&mut k, theorem(&env, d, d, None), &format!("{d} (= {rhs})"));
        }
        let rebuilt = format!("{d}.rebuilt");
        admit(
            &mut k,
            theorem(&env, d, &rebuilt, Some(with_rhs(&env, d, rhs))),
            &rebuilt,
        );
        let flip = if rhs == "Bool.true" {
            "Bool.false"
        } else {
            "Bool.true"
        };
        let forged_name = format!("{d}.forged");
        let forged = theorem(&env, d, &forged_name, Some(with_rhs(&env, d, flip)));
        // Refused as a mismatch of the declared type: the kernel evaluated
        // `chk_LIA` to the other constant. Any other refusal fails the test.
        let refusal = k.add_checked(forged);
        assert!(
            matches!(
                &refusal,
                Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                    source: KernelTypeError::TypeMismatch { .. },
                    ..
                }))
            ),
            "{d} forged to `= {flip}` must be refused as a type mismatch, got {refusal:?}"
        );
        eprintln!("refused\t{forged_name}\ttype mismatch");
    }

    // Ax0's negative control: the planted axiom cannot enter through the entry.
    let planted_ty = env
        .get_const(&n(PLANTED_AXIOM))
        .expect("the fixture declares the planted axiom")
        .type_
        .clone();
    let planted = k.add_checked(Declaration::Axiom {
        name: n(PLANTED_AXIOM),
        level_params: vec![],
        type_: planted_ty,
    });
    assert!(
        matches!(planted, Err(ReferenceRefusal::OutsideAx0 { .. })),
        "{PLANTED_AXIOM} : False must be refused as outside Ax0, got {planted:?}"
    );
    assert!(
        k.add_checked(theorem(&env, PLANTED_THEOREM, PLANTED_THEOREM, None))
            .is_err(),
        "{PLANTED_THEOREM} rests on {PLANTED_AXIOM} and must not enter"
    );
}
