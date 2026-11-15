// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `where` / `let rec` helpers are named declarations, end to end — parse →
//! elaborate → kernel-check → register — on the builtin prelude a
//! Mathlib-free Lean 4.8 file with no imports gets.
//!
//! Lean lifts a helper `go` of `parent` to its own declaration `parent.go`,
//! closed over the locals it captures (`Lean/Elab/LetRec.lean`,
//! `Lean/Elab/MutualDef.lean` `MutualClosure`). Clean inlined the helper as a
//! `let`, so `Memory.readBytes.go mem n addr` (trust-ir
//! `Proofs/MemoryProps.lean`, census at clean `d7f8f959b`) died as "dot
//! notation `.go` on a receiver of type `Memory → Addr → Nat → …`". Every
//! expected shape below was read off the pinned `lean` v4.8.0 with `#check` /
//! `#print`, and every widening has a negative control Lean also rejects.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{BinderInfo, Expr, ExprKind, Name};
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every declaration of `source`
/// on the default (`--prelude builtin`) environment. `Err` carries the first
/// failure, an inner block failure included.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

fn assert_accepts(source: &str, what: &str) -> Environment {
    elaborate_module(source)
        .unwrap_or_else(|e| panic!("{what} must elaborate and kernel-check, but failed:\n{e}"))
}

fn assert_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => panic!("{what} must be rejected (Lean rejects it), but it was accepted"),
        Err(e) => {
            assert!(
                !e.to_lowercase().contains("sorry"),
                "{what}: the rejection must not be laundered into a sorry: {e}"
            );
            e
        }
    }
}

/// `(binder infos, domains)` of a Pi telescope, outermost first.
fn telescope(ty: &Expr) -> (Vec<BinderInfo>, Vec<Expr>) {
    let mut infos = Vec::new();
    let mut domains = Vec::new();
    let mut cur = ty;
    while let ExprKind::Pi(data, dom, body) = cur.kind() {
        infos.push(data.info);
        domains.push((**dom).clone());
        cur = body;
    }
    (infos, domains)
}

fn konst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn decl_type(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be a registered declaration"))
        .type_
        .clone()
}

/// trust-ir `Semantics/Memory.lean` `Memory.readBytes`, in miniature: a
/// structurally recursive `let rec` that reads the parent's `mem`.
const READ_BYTES: &str = "namespace Foo
structure Memory where
  bytes : Nat -> Option Nat

def Memory.readBytes (mem : Memory) (addr : Nat) (n : Nat) : Option (List Nat) :=
  let rec go (remaining : Nat) (currentAddr : Nat) : Option (List Nat) :=
    match remaining with
    | 0 => some []
    | k + 1 =>
      match mem.bytes currentAddr with
      | none => none
      | some b =>
        match go k (currentAddr + 1) with
        | none => none
        | some rest => some (b :: rest)
  go n addr
";

/// Lean v4.8.0: `Foo.Memory.readBytes.go : Foo.Memory → Nat → Nat → Option
/// (List Nat)` — the captured `mem` first, then the helper's own parameters —
/// and `#print Foo.Memory.readBytes` is `fun mem addr n =>
/// Foo.Memory.readBytes.go mem n addr`.
#[test]
fn test_let_rec_lift_captured_local_becomes_leading_parameter() {
    let env = assert_accepts(&format!("{READ_BYTES}end Foo\n"), "Memory.readBytes");
    let go = decl_type(&env, "Foo.Memory.readBytes.go");
    let (infos, domains) = telescope(&go);
    assert_eq!(
        infos,
        vec![BinderInfo::Default; 3],
        "readBytes.go binder infos"
    );
    assert_eq!(
        domains,
        vec![konst("Foo.Memory"), konst("Nat"), konst("Nat")],
        "readBytes.go takes the captured `mem` first, then `remaining`, `currentAddr`"
    );

    // The parent no longer carries the helper inline: under its three
    // lambdas it is exactly `readBytes.go mem n addr`.
    let parent = env
        .get_const(&Name::from_string("Foo.Memory.readBytes"))
        .and_then(|c| c.value.clone())
        .expect("readBytes has a value");
    let mut body = &parent;
    for _ in 0..3 {
        let ExprKind::Lam(_, _, inner) = body.kind() else {
            panic!("readBytes value must be three lambdas, got {parent}");
        };
        body = inner;
    }
    let expected = Expr::apps(
        konst("Foo.Memory.readBytes.go"),
        [Expr::bvar(2), Expr::bvar(0), Expr::bvar(1)],
    );
    assert_eq!(body, &expected, "readBytes body must be `go mem n addr`");
}

/// The proofs trust-ir writes against the helper: name it directly, and
/// unfold the parent to reach it.
#[test]
fn test_let_rec_lift_helper_is_usable_by_name_in_proofs() {
    let src = format!(
        "{READ_BYTES}
theorem readBytes_go_zero (m : Memory) (a : Nat) :
    Memory.readBytes.go m 0 a = some [] := rfl

theorem readBytes_zero (m : Memory) (a : Nat) : m.readBytes a 0 = some [] := by
  simp only [Memory.readBytes]
  exact readBytes_go_zero m a

def firstByte (m : Memory) : Option (List Nat) := Memory.readBytes.go m 1 0
end Foo

theorem go_reads_one : Foo.Memory.readBytes.go ⟨fun _ => some 7⟩ 1 0 = some [7] := rfl
"
    );
    assert_accepts(&src, "proofs naming Memory.readBytes.go");
}

/// NEGATIVE (value): the lifted helper computes what the source says, so a
/// false statement about it is refused — Lean refuses it too.
#[test]
fn test_let_rec_lift_false_value_rejected() {
    let src = format!(
        "{READ_BYTES}end Foo
theorem go_wrong : Foo.Memory.readBytes.go ⟨fun _ => some 7⟩ 1 0 = some [] := rfl
"
    );
    assert_rejected(&src, "a false rfl about readBytes.go");
}

/// NEGATIVE (signature): the captured local is the FIRST parameter, so the
/// helper's own arguments in its place are ill-typed — as in Lean.
#[test]
fn test_let_rec_lift_wrong_parameter_order_rejected() {
    let src = format!(
        "{READ_BYTES}
def bad (m : Memory) : Option (List Nat) := Memory.readBytes.go 1 0 m
end Foo
"
    );
    assert_rejected(&src, "readBytes.go with the captured argument last");
}

/// NEGATIVE (name): only the helper the source declares exists.
#[test]
fn test_let_rec_lift_undeclared_helper_name_rejected() {
    let src = format!(
        "{READ_BYTES}
def bad (m : Memory) : Option (List Nat) := Memory.readBytes.loop m 1 0
end Foo
"
    );
    assert_rejected(&src, "a helper name the source never declared");
}

/// A `where` helper (Lean desugars `where` to a leading `let rec` group):
/// `readW.go : (Nat → Option Nat) → Nat → Nat → Option (List Nat)`.
#[test]
fn test_let_rec_lift_where_helper_is_named() {
    let src = "def readW (bytes : Nat -> Option Nat) (n : Nat) : Option (List Nat) :=
  go n 0
where
  go (remaining : Nat) (currentAddr : Nat) : Option (List Nat) :=
    match remaining with
    | 0 => some []
    | k + 1 =>
      match bytes currentAddr with
      | none => none
      | some b =>
        match go k (currentAddr + 1) with
        | none => none
        | some rest => some (b :: rest)

def useW (bytes : Nat -> Option Nat) : Option (List Nat) := readW.go bytes 3 0
";
    let env = assert_accepts(src, "a `where` helper used by name");
    let (_, domains) = telescope(&decl_type(&env, "readW.go"));
    assert_eq!(
        domains.len(),
        3,
        "readW.go: captured `bytes`, `remaining`, `currentAddr`"
    );
    assert_eq!(domains[1], konst("Nat"));
    assert_eq!(domains[2], konst("Nat"));
}

/// Lean v4.8.0: `@withLet.aux : {α : Type} → List α → Nat → Nat → Nat` — a
/// captured implicit stays implicit, and a captured `let` variable (`k`)
/// becomes an explicit parameter.
#[test]
fn test_let_rec_lift_keeps_implicit_and_captures_let_variable() {
    let src = "def withLet {α : Type} (xs : List α) (n : Nat) : Nat :=
  let k := n + 1
  let rec aux (m : Nat) : Nat :=
    match m with
    | 0 => k + xs.length
    | j + 1 => aux j
  aux n

theorem withLet_aux_val : withLet.aux [1, 2] 5 3 = 7 := rfl
";
    let env = assert_accepts(src, "withLet.aux");
    let (infos, _) = telescope(&decl_type(&env, "withLet.aux"));
    assert_eq!(
        infos,
        vec![
            BinderInfo::Implicit,
            BinderInfo::Default,
            BinderInfo::Default,
            BinderInfo::Default
        ],
        "withLet.aux binder infos"
    );
    assert_rejected(
        &src.replace("= 7 := rfl", "= 8 := rfl"),
        "a false value of withLet.aux",
    );
}

/// Sibling `where` helpers: `two` calls `one`, which captures `n`, so `two`
/// captures `n` too and its value names `sib.one` (Lean's `mkFreeVarMap`).
/// Non-recursive helpers lift as well.
#[test]
fn test_let_rec_lift_sibling_helpers_share_captures() {
    let src = "def sib (n : Nat) : Nat := two 1
where
  one (x : Nat) : Nat := x + n
  two (y : Nat) : Nat := one y + one y

theorem sib_one_val : sib.one 10 1 = 11 := rfl
theorem sib_two_val : sib.two 10 1 = 22 := rfl
";
    let env = assert_accepts(src, "sibling where helpers");
    for name in ["sib.one", "sib.two"] {
        let (_, domains) = telescope(&decl_type(&env, name));
        assert_eq!(
            domains,
            vec![konst("Nat"), konst("Nat")],
            "{name} : Nat → Nat → Nat"
        );
    }
    let two = env
        .get_const(&Name::from_string("sib.two"))
        .and_then(|c| c.value.clone())
        .expect("sib.two has a value");
    let mut names = std::collections::HashSet::new();
    two.collect_constants_into(&mut names);
    assert!(
        names.contains(&Name::from_string("sib.one")),
        "sib.two must call sib.one, not an inlined copy: {two}"
    );
}

fn constant_kind(env: &Environment, name: &str) -> clean_kernel::ConstantKind {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be a registered declaration"))
        .kind
}

/// `pp.go` of a `partial def` with a recursive `where` helper.
const PARTIAL_PP: &str = "partial def pp (n : Nat) : Nat := go n
where go : Nat → Nat
  | 0 => 0
  | k+1 => go k
";

/// Lean v4.8.0: `#print pp.go` is `opaque pp.go : Nat → Nat` — the recursive
/// helper of a `partial` declaration is added by `addAndCompilePartial`, so
/// it does not reduce — while the parent, which is not itself recursive,
/// stays an ordinary definition.
#[test]
fn test_let_rec_lift_partial_recursive_helper_is_opaque() {
    let env = assert_accepts(PARTIAL_PP, "a partial def with a recursive helper");
    assert_eq!(
        constant_kind(&env, "pp.go"),
        clean_kernel::ConstantKind::Opaque
    );
    assert_eq!(
        constant_kind(&env, "pp"),
        clean_kernel::ConstantKind::Definition
    );
}

/// NEGATIVE (reduction): `theorem t1 : pp.go 3 = 0 := rfl` and `theorem t2 :
/// pp 3 = 0 := rfl` are both `type mismatch` in Lean v4.8.0, because
/// `pp.go` is opaque. Clean accepted both while the helper was a reducible
/// definition (and, before the lift, while it was an inline `let`).
#[test]
fn test_let_rec_lift_partial_helper_does_not_reduce_rejected() {
    assert_rejected(
        &format!("{PARTIAL_PP}theorem t1 : pp.go 3 = 0 := rfl\n"),
        "rfl through the opaque pp.go",
    );
    assert_rejected(
        &format!("{PARTIAL_PP}theorem t2 : pp 3 = 0 := rfl\n"),
        "rfl through pp into the opaque pp.go",
    );
}

/// Control: the same helper under a NON-partial parent is structural
/// recursion and reduces (Lean v4.8.0 accepts `qq.go 3 = 0 := rfl`).
#[test]
fn test_let_rec_lift_total_helper_reduces() {
    let env = assert_accepts(
        "def qq (n : Nat) : Nat := go n
where go : Nat → Nat
  | 0 => 0
  | k+1 => go k

theorem t3 : qq.go 3 = 0 := rfl
theorem t4 : qq 3 = 0 := rfl
",
        "rfl through a total helper",
    );
    assert_eq!(
        constant_kind(&env, "qq.go"),
        clean_kernel::ConstantKind::Definition
    );
}

/// Lean's `mkInhabitantFor`: an `Inhabited` instance of the result type
/// (`py.go`), or a parameter of that type (`pa.go`, whose captured `seed` is
/// its first parameter: `opaque pa.go : NoInst → Nat → NoInst`), lets the opaque be
/// added; a NON-recursive helper of a `partial` parent is an ordinary
/// definition that reduces (`pnr.go`, Lean `isNonRecursive`). Pinned v4.8.0:
/// `opaque py.go`, `opaque pa.go`, `def pnr.go`, and `tnr` checks.
#[test]
fn test_let_rec_lift_partial_helper_inhabited_or_nonrecursive_passes() {
    let env = assert_accepts(
        "structure YesInst where
  n : Nat
instance : Inhabited YesInst := ⟨⟨0⟩⟩
partial def py (n : Nat) : Nat := (go n).n
where go : Nat → YesInst
  | 0 => ⟨0⟩
  | k+1 => go k

structure NoInst where
  n : Nat
partial def pa (n : Nat) (seed : NoInst) : Nat := (go n).n
where go : Nat → NoInst
  | 0 => seed
  | k+1 => go k

partial def pnr (n : Nat) : Nat := go n
where go (k : Nat) : Nat := k + 1

theorem tnr : pnr.go 3 = 4 := rfl
",
        "partial helpers Lean accepts",
    );
    for name in ["py.go", "pa.go"] {
        assert_eq!(
            constant_kind(&env, name),
            clean_kernel::ConstantKind::Opaque,
            "{name}"
        );
    }
    assert_eq!(
        constant_kind(&env, "pnr.go"),
        clean_kernel::ConstantKind::Definition
    );
}

/// NEGATIVE (inhabitation): no instance, no parameter of the result type —
/// Lean v4.8.0: "failed to compile partial definition 'pn.go', failed to show
/// that type is inhabited and non empty". An opaque of an uninhabited type
/// would be an axiom; Clean refuses it too.
#[test]
fn test_let_rec_lift_partial_helper_uninhabited_rejected() {
    let error = assert_rejected(
        "structure NoInst where
  n : Nat
partial def pn (n : Nat) : Nat := (go n).n
where go : Nat → NoInst
  | 0 => ⟨0⟩
  | k+1 => go k
",
        "an uninhabited partial helper",
    );
    assert!(error.contains("pn.go"), "{error}");
}

/// NEGATIVE (names): a helper whose name is already declared, and a second
/// helper of the same name in one declaration — even an identical one — are
/// refused. Pinned v4.8.0: `'foo.go' has already been declared`, and the same
/// for `bar.go` and `baz.go`.
#[test]
fn test_let_rec_lift_duplicate_helper_names_rejected() {
    let declared = assert_rejected(
        "def foo.go : Nat := 1
def foo (n : Nat) : Nat := go n
where go : Nat → Nat
  | 0 => 0
  | k+1 => go k
",
        "a helper named like an existing declaration",
    );
    assert!(
        declared.contains("foo.go") && declared.contains("already been declared"),
        "{declared}"
    );
    for (name, other_zero) in [("bar", "1"), ("baz", "0")] {
        let src = format!(
            "def {name} (b : Bool) : Nat :=
  if b then
    let rec go : Nat → Nat | 0 => 0 | k+1 => go k
    go 1
  else
    let rec go : Nat → Nat | 0 => {other_zero} | k+1 => go k
    go 2
"
        );
        let error = assert_rejected(&src, "two helpers of one name");
        assert!(error.contains("already been declared"), "{name}: {error}");
    }
}

/// Named arguments: on the parent of a helper (its binder names are the
/// parent's, not lost to the helper), and on the helper itself (its captured
/// locals, then its own parameters, as Lean names them in its type). Pinned
/// v4.8.0: all four check.
#[test]
fn test_let_rec_lift_named_arguments_on_parent_and_helper_pass() {
    assert_accepts(
        "def named (a : Nat) (b : Nat) : Nat := go b
where go (k : Nat) : Nat := a + k

def useNamed : Nat := named.go (a := 1) (k := 2)
def callNamed : Nat := named (b := 2) (a := 1)
theorem tn : useNamed = 3 := rfl
theorem tc : callNamed = 3 := rfl

def named2 (a : Nat) : Nat := go a
where go : Nat → Nat
  | 0 => a
  | k+1 => go k

def useNamed2 : Nat := named2.go (a := 5) 3
theorem tn2 : useNamed2 = 5 := rfl
",
        "named arguments around a lifted helper",
    );
}

/// NEGATIVE (named arguments): a name the helper's type does not give.
#[test]
fn test_let_rec_lift_unknown_named_argument_rejected() {
    assert_rejected(
        "def named (a : Nat) (b : Nat) : Nat := go b
where go (k : Nat) : Nat := a + k

def bad : Nat := named.go (a := 1) (z := 2)
",
        "an unknown named argument on a helper",
    );
}

/// Size of the intermediate form: each helper calls the one before it twice,
/// so a helper's closed value, read as a TREE, holds 2^k copies of the first
/// one (the copies are shared; Lean substitutes a constant application
/// instead). A walk over the term that visits every path takes time
/// exponential in the chain: the closure's free-variable scan did, at 0.44 s
/// for depth 16, 7.45 s for 24 and more than 60 s for 32 (release `clean
/// check`, measured 2026-10-08). At depth 28 that is minutes in a debug test
/// build; a walk that visits each shared node once takes well under a second,
/// so the bound below has two orders of magnitude of slack either way.
#[test]
fn test_let_rec_lift_doubling_sibling_chain_elaborates() {
    let depth = 28;
    let mut src =
        format!("def chain (n : Nat) : Nat := h{depth} n\nwhere\n  h0 (x : Nat) : Nat := x + n\n");
    for k in 1..=depth {
        src.push_str(&format!(
            "  h{k} (x : Nat) : Nat := h{prev} x + h{prev} x\n",
            prev = k - 1
        ));
    }
    let start = std::time::Instant::now();
    let env = assert_accepts(&src, "a doubling chain of sibling helpers");
    let elapsed = start.elapsed();
    eprintln!("doubling sibling chain depth {depth}: elaborated in {elapsed:?}");
    assert!(env
        .get_const(&Name::from_string(&format!("chain.h{depth}")))
        .is_some());
    assert!(
        elapsed < std::time::Duration::from_secs(120),
        "depth {depth} took {elapsed:?}: a pass walks the lifted helpers as a tree"
    );
}

/// A `let rec` under `fun {β} b =>` captures `β` and `b`. Lean's closure
/// (`mkClosureForAux`) keeps each captured local's binder info, so pinned
/// v4.8.0 reads `@capI.go : {β : Type} → β → Nat → List β` and accepts
/// `capI.go 1 2 = [1, 1] := rfl`. Clean made every captured local that was
/// not a declaration parameter explicit, so it took `capI.go Nat 1 2` —
/// which Lean refuses (`application type mismatch`) — as the call.
const CAPTURE_LAMBDA_IMPLICIT: &str = "def capI : {β : Type} → β → List β := fun {β} b =>
  let rec go (n : Nat) : List β :=
    match n with
    | 0 => []
    | k + 1 => b :: go k
  go 2

theorem capI_go_val : capI.go 1 2 = [1, 1] := rfl
";

#[test]
fn test_let_rec_lift_captured_lambda_implicit_stays_implicit() {
    let env = assert_accepts(CAPTURE_LAMBDA_IMPLICIT, "capI.go");
    let (infos, _) = telescope(&decl_type(&env, "capI.go"));
    assert_eq!(
        infos,
        vec![
            BinderInfo::Implicit,
            BinderInfo::Default,
            BinderInfo::Default
        ],
        "capI.go binder infos"
    );
}

/// NEGATIVE: the auxiliary's full telescope, spelled out with `@`, starts
/// with the implicit `β` (pinned v4.8.0 `@capI.go 1 2`: `failed to synthesize
/// instance`), and a false value (`type mismatch`).
#[test]
fn test_let_rec_lift_captured_lambda_implicit_negatives_rejected() {
    assert_rejected(
        &format!("{CAPTURE_LAMBDA_IMPLICIT}def capI_bad := @capI.go 1 2\n"),
        "capI.go's explicit telescope starting at a value",
    );
    assert_rejected(
        &CAPTURE_LAMBDA_IMPLICIT.replace("capI.go 1 2 = [1, 1]", "capI.go 1 2 = [2, 2]"),
        "a false value of capI.go",
    );
}

/// A captured `fun [inst : Inhabited α]` local stays instance-implicit:
/// pinned v4.8.0 `@capInst.go : {α : Type} → [inst : Inhabited α] → Nat →
/// List α`, and `capInst.go (α := Nat) 2 = [0, 0] := rfl` checks.
const CAPTURE_LAMBDA_INST: &str = "def capInst : {α : Type} → [Inhabited α] → Nat → List α :=
  fun {α} [inst : Inhabited α] n =>
  let rec go (k : Nat) : List α :=
    match k with
    | 0 => []
    | j + 1 => default :: go j
  go n

theorem capInst_go_val : capInst.go (α := Nat) 2 = [0, 0] := rfl
";

#[test]
fn test_let_rec_lift_captured_lambda_instance_stays_instance_implicit() {
    let env = assert_accepts(CAPTURE_LAMBDA_INST, "capInst.go");
    let (infos, _) = telescope(&decl_type(&env, "capInst.go"));
    assert_eq!(
        infos,
        vec![
            BinderInfo::Implicit,
            BinderInfo::InstImplicit,
            BinderInfo::Default
        ],
        "capInst.go binder infos"
    );
}

/// NEGATIVE: the full telescope with `@` starts at the implicit `α`
/// (pinned v4.8.0 `@capInst.go 2`: `failed to synthesize instance`), and a
/// false value (`type mismatch`).
#[test]
fn test_let_rec_lift_captured_lambda_instance_negatives_rejected() {
    assert_rejected(
        &format!("{CAPTURE_LAMBDA_INST}def capInst_bad := @capInst.go 2\n"),
        "capInst.go's explicit telescope starting at a value",
    );
    assert_rejected(
        &CAPTURE_LAMBDA_INST.replace(
            "capInst.go (α := Nat) 2 = [0, 0]",
            "capInst.go (α := Nat) 2 = [0, 0, 0]",
        ),
        "a false value of capInst.go",
    );
}

/// `fun xs =>` against `{β : Type} → List β → Nat`: the implicit-lambda rule
/// introduces `β` (Lean's `elabImplicitLambda`) as an IMPLICIT local, which
/// the `let rec` captures through `xs`. Pinned v4.8.0: `@capAuto.go : {β :
/// Type} → List β → Nat → Nat`, `capAuto.go [1, 2, 3] 5 = 3 := rfl` checks.
const CAPTURE_AUTO_IMPLICIT: &str = "def capAuto : {β : Type} → List β → Nat := fun xs =>
  let rec go (n : Nat) : Nat :=
    match n with
    | 0 => xs.length
    | k + 1 => go k
  go 4

theorem capAuto_go_val : capAuto.go [1, 2, 3] 5 = 3 := rfl
";

#[test]
fn test_let_rec_lift_captured_implicit_lambda_local_stays_implicit() {
    let env = assert_accepts(CAPTURE_AUTO_IMPLICIT, "capAuto.go");
    let (infos, _) = telescope(&decl_type(&env, "capAuto.go"));
    assert_eq!(
        infos,
        vec![
            BinderInfo::Implicit,
            BinderInfo::Default,
            BinderInfo::Default
        ],
        "capAuto.go binder infos"
    );
}

/// NEGATIVE: the introduced `β` by name (pinned v4.8.0: `invalid argument
/// name 'β'` — the implicit lambda's local is inaccessible), and the full
/// telescope with `@` starting at a list (`application type mismatch`).
#[test]
fn test_let_rec_lift_captured_implicit_lambda_local_negatives_rejected() {
    assert_rejected(
        &CAPTURE_AUTO_IMPLICIT.replace(
            "capAuto.go [1, 2, 3] 5 = 3",
            "capAuto.go (β := Nat) [1, 2, 3] 5 = 3",
        ),
        "capAuto.go with its inaccessible implicit named",
    );
    assert_rejected(
        &format!("{CAPTURE_AUTO_IMPLICIT}def capAuto_bad := @capAuto.go [1, 2, 3] 5\n"),
        "capAuto.go's explicit telescope starting at a list",
    );
}

/// NEGATIVE: each captured implicit passed explicitly. Pinned v4.8.0 and
/// v4.30.0-rc2 refuse all three (`function expected` / `application type
/// mismatch`, re-run 2026-11-14), as does the registered
/// `{β : Type} → β → Nat → List β` taken as written. Clean accepted them by
/// ledger class (73) -- the application elaborator took an explicit argument
/// at a leading IMPLICIT binder (`try_consume_leading_implicit_args`) -- until
/// commit 8c866b7fe removed that consumption; pinned ACCEPTED until
/// 2026-11-14, asserted REJECTED since.
#[test]
fn test_let_rec_lift_captured_implicit_passed_explicitly_rejected() {
    assert_rejected(
        &format!("{CAPTURE_LAMBDA_IMPLICIT}def capI_bad := capI.go Nat 1 2\n"),
        "capI.go Nat 1 2",
    );
    assert_rejected(
        &format!("{CAPTURE_LAMBDA_INST}def capInst_bad := capInst.go Nat ⟨0⟩ 2\n"),
        "capInst.go Nat ⟨0⟩ 2",
    );
    assert_rejected(
        &format!("{CAPTURE_AUTO_IMPLICIT}def capAuto_bad := capAuto.go Nat [1, 2, 3] 5\n"),
        "capAuto.go Nat [1, 2, 3] 5",
    );
}

/// A recursive helper the `partial` parent never calls is still declared:
/// pinned v4.8.0 `#print pu.go` is `opaque pu.go : Nat → Nat`, and `pu` is
/// `fun n => n`. The declaration boundary refuses a recursive helper of a
/// `partial` parent that reaches it in neither lifted nor inline form, so
/// this pins that an unused helper still arrives lifted and registers.
#[test]
fn test_let_rec_lift_partial_unused_recursive_helper_is_opaque() {
    let env = assert_accepts(
        "partial def pu (n : Nat) : Nat := n
where go : Nat → Nat
  | 0 => 0
  | k+1 => go k
",
        "a partial def with an unused recursive helper",
    );
    assert_eq!(
        constant_kind(&env, "pu.go"),
        clean_kernel::ConstantKind::Opaque
    );
}
