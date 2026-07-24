// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Track AA regression tests: a NON-degenerate nested-mutual fold.
//!
//! A `mutual` block of the shape
//!
//! ```text
//! inductive Tree | leaf : Nat -> Tree | node : List Tree -> Tree
//! mutual
//!   def Tree.size : Tree -> Nat
//!     | leaf n  => n
//!     | node ts => Tree.sizeList ts
//!   def Tree.sizeList : List Tree -> Nat
//!     | []        => 0
//!     | t :: rest => Tree.size t + Tree.sizeList rest
//! end
//! ```
//!
//! is FUSED into ONE `Tree.rec` application: `Tree.size`'s arms supply the
//! primary minors (`leaf`/`node`), and `Tree.sizeList`'s arms supply the
//! restored auxiliary minors (`List.nil`/`.cons`, exposed by `Tree.rec_1`) — a
//! GENUINE fold. The node minor
//! body `Tree.sizeList ts` becomes the auxiliary-motive IH `ih_ts`; the cons
//! minor body `Tree.size t + Tree.sizeList rest` becomes `ih_t + ih_rest`, with
//! each field's induction hypothesis read off the restored companion recursor
//! (`Tree.rec_1`).
//!
//! Wave 5 / Track U lowered the SINGLE-function nested recursion but filled the
//! auxiliary minors with a SOUND-but-DEGENERATE default (`Nat.zero` base), so
//! `Tree.size (node [leaf 2, leaf 3])` reduced to `0`, not the true sum `5`.
//! These tests assert the fused fold reduces to the REAL sum and that every
//! synthesized definition kernel-checks with an EMPTY axiom closure (no `sorry`,
//! no faked termination axiom — the genuine mutual `Tree.rec`).

use crate::elaborate_decl_and_register;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, TypeChecker};
use clean_parser::parse_file;

/// Elaborate + register every decl in `code` into a fresh prelude env.
fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        if let clean_parser::SurfaceDecl::RawDecl { content, span } = decl {
            panic!("decl {i} fell through to RawDecl (parser error recovery): content={content:?}, span={span:?}");
        }
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

/// Assert a constant is registered, its value kernel-checks (`infer_type`
/// succeeds and is def-eq to the declared type), and its axiom closure is EMPTY.
fn assert_sound_const(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let info = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{name} should be registered"));

    let value = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should be a definition with a value"));
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(value)
        .unwrap_or_else(|e| panic!("infer_type({name}.value) failed: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{name}: inferred value type not def-eq to declared type"
    );

    let deps = env
        .axiom_deps(&n)
        .unwrap_or_else(|| panic!("{name} is registered, axiom_deps should return Some"));
    let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "{name} must have an EMPTY axiom closure (sound fused nested-mutual recursion), got {dep_names:?}"
    );
}

/// Whnf-reduce `expr` and assert it is def-eq to the `Nat` literal `expected` —
/// forcing the recursor's iota-reduction to actually fire (the `rfl`
/// computational check, at the kernel level).
fn assert_reduces_to_nat(env: &Environment, expr: Expr, expected: u64) {
    let tc = TypeChecker::new(env);
    let lit = Expr::nat_lit(expected);
    assert!(
        tc.is_def_eq(&expr, &lit),
        "expected reduction to Nat {expected}, but whnf = {:?}",
        tc.whnf(&expr)
    );
}

fn const0(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn tree_list_nil() -> Expr {
    Expr::app(
        Expr::const_(
            Name::from_string("List.nil"),
            vec![clean_kernel::Level::zero()],
        ),
        const0("Tree"),
    )
}

fn tree_list_cons(elem: Expr, tail: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("List.cons"),
                    vec![clean_kernel::Level::zero()],
                ),
                const0("Tree"),
            ),
            elem,
        ),
        tail,
    )
}

const TREE_FOLD: &str = r#"
inductive Tree where
  | leaf : Nat -> Tree
  | node : List Tree -> Tree

mutual
  def Tree.size : Tree -> Nat
    | leaf n  => n
    | node ts => Tree.sizeList ts
  def Tree.sizeList : List Tree -> Nat
    | []        => 0
    | t :: rest => Tree.size t + Tree.sizeList rest
end
"#;

const TREE_FUNCTION_FOLD: &str = r#"
inductive Tree where
  | leaf : Nat -> Tree
  | node : List Tree -> Tree

mutual
  def Tree.run : Tree -> Nat -> Nat
    | leaf _  => fun acc => acc
    | node ts => Tree.runList ts
  def Tree.runList : List Tree -> Nat -> Nat
    | []        => fun acc => acc
    | _ :: rest => Tree.runList rest
end
"#;

/// CORE Track AA gate: both fused members kernel-check with an empty axiom
/// closure, and `Tree.size` over a multi-element node reduces to the TRUE sum.
#[test]
fn test_nested_mutual_fold_sound_and_nondegenerate() {
    let env = elab_all(TREE_FOLD);
    assert_sound_const(&env, "Tree.size");
    assert_sound_const(&env, "Tree.sizeList");

    // leaf: Tree.size (leaf 7) = 7 (primary leaf minor).
    let leaf7 = Expr::app(const0("Tree.leaf"), Expr::nat_lit(7u64));
    assert_reduces_to_nat(&env, Expr::app(const0("Tree.size"), leaf7), 7);

    // node-nil: Tree.size (node []) = 0 (node minor → auxiliary nil minor).
    let node_nil = Expr::app(const0("Tree.node"), tree_list_nil());
    assert_reduces_to_nat(&env, Expr::app(const0("Tree.size"), node_nil), 0);

    // node [leaf 2, leaf 3]: the REAL fold. node minor → aux cons minor twice
    // → 2 + (3 + 0) = 5. A degenerate (Nat.zero base) fold would give 0.
    let leaf = |n: u64| Expr::app(const0("Tree.leaf"), Expr::nat_lit(n));
    let payload = tree_list_cons(leaf(2), tree_list_cons(leaf(3), tree_list_nil()));
    let node = Expr::app(const0("Tree.node"), payload);
    assert_reduces_to_nat(&env, Expr::app(const0("Tree.size"), node), 5);
}

/// A nested-rec minor binds exactly its constructor fields and IHs. Its motive
/// conclusion may itself be a function; that result Pi must remain intact
/// rather than being peeled and misclassified as another IH binder.
#[test]
fn test_nested_mutual_fold_function_result_preserves_result_telescope() {
    let env = elab_all(TREE_FUNCTION_FOLD);

    // `assert_sound_const` checks the declaration's own axiom closure.  That is
    // deterministic under parallel test execution, unlike the process-global
    // sorry counters (which can observe unrelated tests running concurrently).
    assert_sound_const(&env, "Tree.run");
    assert_sound_const(&env, "Tree.runList");

    let leaf = |n: u64| Expr::app(const0("Tree.leaf"), Expr::nat_lit(n));
    let leaf_run = Expr::app(Expr::app(const0("Tree.run"), leaf(2)), Expr::nat_lit(3u64));
    assert_reduces_to_nat(&env, leaf_run, 3);

    let payload = tree_list_cons(leaf(2), tree_list_cons(leaf(3), tree_list_nil()));
    let node = Expr::app(const0("Tree.node"), payload);
    let node_run = Expr::app(Expr::app(const0("Tree.run"), node), Expr::nat_lit(1u64));
    assert_reduces_to_nat(&env, node_run, 1);
}

/// The reduction check is REAL, not vacuous: asserting the wrong sum panics.
/// (A degenerate fold would reduce to 0; the genuine fold reduces to 5; either
/// way, claiming 6 must fail.)
#[test]
#[should_panic(expected = "expected reduction to Nat 6")]
fn test_nested_mutual_fold_reduction_is_real_negative_control() {
    let env = elab_all(TREE_FOLD);
    let leaf = |n: u64| Expr::app(const0("Tree.leaf"), Expr::nat_lit(n));
    let payload = tree_list_cons(leaf(2), tree_list_cons(leaf(3), tree_list_nil()));
    let node = Expr::app(const0("Tree.node"), payload);
    // The real sum is 5, NOT 6 — this MUST panic, proving the fold genuinely
    // computes (not a vacuous / degenerate check).
    assert_reduces_to_nat(&env, Expr::app(const0("Tree.size"), node), 6);
}

/// A single-element node reduces through exactly one aux cons minor.
#[test]
fn test_nested_mutual_fold_single_element() {
    let env = elab_all(TREE_FOLD);
    let leaf = |n: u64| Expr::app(const0("Tree.leaf"), Expr::nat_lit(n));
    let payload = tree_list_cons(leaf(9), tree_list_nil());
    let node = Expr::app(const0("Tree.node"), payload);
    // node [leaf 9] → 9 + 0 = 9.
    assert_reduces_to_nat(&env, Expr::app(const0("Tree.size"), node), 9);
}

/// The fusion must not regress an ordinary plain-ident mutual block over the
/// SAME inductive (Nat) — that still lowers through the product-packing path.
#[test]
fn test_plain_mutual_block_still_works_alongside_nested() {
    let env = elab_all(
        r#"
mutual
def isEven : Nat -> Bool
  | Nat.zero => true
  | Nat.succ n => isOdd n
def isOdd : Nat -> Bool
  | Nat.zero => false
  | Nat.succ n => isEven n
end
"#,
    );
    assert_sound_const(&env, "isEven");
    assert_sound_const(&env, "isOdd");
    let tc = TypeChecker::new(&env);
    let even2 = Expr::app(const0("isEven"), Expr::nat_lit(2u64));
    assert!(
        tc.is_def_eq(&even2, &const0("Bool.true")),
        "isEven 2 should reduce to true"
    );
}
