// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for RC insertion pass.
//! Part of #963 - Compiler IR infrastructure.

use super::*;
use crate::lcnf::Param;
use crate::rc::borrow::infer_borrow;

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn nat_type() -> Expr {
    Expr::const_str("Nat")
}

#[test]
fn test_simple_return_borrowed_param_gets_inc() {
    // def id (x : Nat) : Nat := return x
    // x is borrowed (inferred by borrow analysis). Returning a borrowed param
    // requires inc per Lean 4 ExplicitRC.lean line 615.
    let decl = Decl::new(
        name("id"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );

    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);

    let s = format!("{:?}", result.body);
    assert!(
        s.contains("_inc"),
        "Returning borrowed param should generate inc: {s}"
    );
}

#[test]
fn test_constructor_args_inc() {
    // def wrap (x : Nat) : Box Nat :=
    //   let _1 := Box.mk x
    //   return _1
    // x is owned (consumed by ctor), needs inc
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::Ctor {
                name: name("Box.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );

    let decl = Decl::new(
        name("wrap"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        code,
        false,
    );

    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);

    // Should have inc for x
    let s = format!("{:?}", result.body);
    assert!(s.contains("_inc"), "Should have inc: {s}");
}

#[test]
fn test_live_vars() {
    let mut live = LiveVars::new();
    live.mark_live(fvar(1));
    live.mark_live(fvar(2));

    assert!(live.is_live(fvar(1)));
    assert!(live.is_live(fvar(2)));
    assert!(!live.is_live(fvar(3)));

    live.mark_dead(fvar(1));
    assert!(!live.is_live(fvar(1)));
}

#[test]
fn test_borrowed_vars_skip_rc() {
    let mut live = LiveVars::new();
    live.mark_borrowed(fvar(1));

    assert!(live.is_borrowed(fvar(1)));
    assert!(!live.is_borrowed(fvar(2)));
}

// Part of #2014: Scalar type exclusion tests

#[test]
fn test_is_scalar_type_known_scalars() {
    assert!(is_scalar_type(&Expr::const_str("Bool")));
    assert!(is_scalar_type(&Expr::const_str("UInt8")));
    assert!(is_scalar_type(&Expr::const_str("UInt16")));
    assert!(is_scalar_type(&Expr::const_str("UInt32")));
    assert!(is_scalar_type(&Expr::const_str("UInt64")));
    assert!(is_scalar_type(&Expr::const_str("USize")));
    assert!(is_scalar_type(&Expr::const_str("Float")));
    assert!(is_scalar_type(&Expr::const_str("Float32")));
    assert!(is_scalar_type(&Expr::const_str("Float64")));
    assert!(is_scalar_type(&Expr::const_str("Char")));
    assert!(is_scalar_type(&Expr::const_str("Unit")));
    assert!(is_scalar_type(&Expr::const_str("PUnit")));
}

#[test]
fn test_is_scalar_type_reference_types() {
    assert!(!is_scalar_type(&Expr::const_str("Nat")));
    assert!(!is_scalar_type(&Expr::const_str("String")));
    assert!(!is_scalar_type(&Expr::const_str("List")));
    assert!(!is_scalar_type(&Expr::const_str("Array")));
    assert!(!is_scalar_type(&Expr::const_str("_")));
}

#[test]
fn test_scalar_param_skips_rc() {
    // def inc_u64 (x : UInt64) : UInt64 :=
    //   let _1 := Pair.mk x x  -- ctor consuming scalar args
    //   return _1
    // x is UInt64 (scalar), no inc should be emitted
    let uint64_type = Expr::const_str("UInt64");
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Pair"),
            LetValue::Ctor {
                name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );

    let decl = Decl::new(
        name("inc_u64"),
        vec![],
        uint64_type.clone(),
        vec![Param::new(fvar(0), name("x"), uint64_type)],
        code,
        false,
    );

    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);

    // Should NOT have inc for x (scalar type)
    let s = format!("{:?}", result.body);
    assert!(
        !s.contains("_inc"),
        "Scalar UInt64 param should NOT get inc: {s}"
    );
}

#[test]
fn test_object_param_gets_rc() {
    // def wrap (x : Nat) : Pair :=
    //   let _1 := Pair.mk x x
    //   return _1
    // x is Nat (object type), inc should be emitted
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            Expr::const_str("Pair"),
            LetValue::Ctor {
                name: name("Pair.mk"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );

    let decl = Decl::new(
        name("wrap"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        code,
        false,
    );

    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);

    // Should have inc for x (Nat is object type)
    let s = format!("{:?}", result.body);
    assert!(s.contains("_inc"), "Nat param should get inc: {s}");
}

#[test]
fn test_scalar_let_var_skips_dec() {
    // def f (x : Bool) : Nat :=
    //   let b : Bool := ...
    //   -- b is Bool (scalar), should not be dec'd when dead
    //   return x
    let bool_type = Expr::const_str("Bool");
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("b"),
            bool_type,
            LetValue::Lit(clean_kernel::Literal::Nat(clean_kernel::BigNat::Small(0))),
        ),
        Code::ret(fvar(0)),
    );

    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        code,
        false,
    );

    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);

    // No dec for b (scalar Bool)
    let s = format!("{:?}", result.body);
    assert!(
        !s.contains("_dec"),
        "Scalar Bool var should NOT get dec: {s}"
    );
}

#[test]
fn test_needs_rc_with_type_map() {
    let borrow_map = BorrowMap::new();
    let mut ctx = RCContext::new(&borrow_map);
    let live = LiveVars::new();

    // Register a scalar type
    ctx.register_type(fvar(1), &Expr::const_str("UInt64"));
    assert!(!ctx.needs_rc(fvar(1), &live), "Scalar should not need RC");

    // Register an object type
    ctx.register_type(fvar(2), &Expr::const_str("Nat"));
    assert!(ctx.needs_rc(fvar(2), &live), "Object should need RC");

    // Unknown type (not registered) defaults to needing RC
    assert!(ctx.needs_rc(fvar(3), &live), "Unknown should need RC");
}

// --- Algorithm audit: P1-720 ---

/// Lean 4 ExplicitRC.lean line 615: returning a borrowed param requires inc.
/// The inc transfers ownership to the return value while the caller retains
/// its borrowed reference. Requires fix in insert_rc_return (mod.rs).
#[test]
fn test_borrowed_return_needs_inc() {
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        Code::ret(fvar(0)),
        false,
    );

    let mut borrow_map = BorrowMap::new();
    borrow_map.insert(
        name("f"),
        crate::rc::borrow::FnBorrow {
            params: vec![Ownership::Borrowed],
        },
    );
    let result = insert_rc(&decl, &borrow_map);

    let s = format!("{:?}", result.body);
    assert!(
        s.contains("_inc"),
        "Returning borrowed param must generate inc (Lean 4 ExplicitRC line 615): {s}"
    );
}

/// Lean 4 ExplicitRC: addDecIfNeeded frees dead let-bound reference values.
/// Without this, objects returned by calls but never used leak memory.
/// Requires fix in Code::Let handler (mod.rs).
#[test]
fn test_dead_let_value_needs_dec() {
    // let _1 := g(x); return x  -- _1 is never used, must be dec'd
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::Const {
                name: name("g"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(0)),
    );

    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        code,
        false,
    );

    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);

    let s = format!("{:?}", result.body);
    assert!(
        s.contains("_dec"),
        "Dead let-bound value must be dec'd (Lean 4 addDecIfNeeded): {s}"
    );
}

/// P3: Duplicate args in consuming positions generate extra inc/dec pair.
/// Lean 4 uses isFirstOcc + getNumConsumptions for optimal inc count.
/// clean increments per-arg occurrence, producing an extra inc + compensating dec.
/// Functionally correct (extra ops cancel out) but suboptimal.
#[test]
fn test_duplicate_arg_inc_dec_balance() {
    // let _1 := f(x, x); return _1  -- x used twice, dead after call
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("_1"),
            nat_type(),
            LetValue::Const {
                name: name("f"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0)), Arg::FVar(fvar(0))],
            },
        ),
        Code::ret(fvar(1)),
    );

    let decl = Decl::new(
        name("g"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("x"), nat_type())],
        code,
        false,
    );

    // Make f's params both owned
    let mut borrow_map = infer_borrow(std::slice::from_ref(&decl));
    borrow_map.insert(
        name("f"),
        crate::rc::borrow::FnBorrow {
            params: vec![Ownership::Owned, Ownership::Owned],
        },
    );
    let result = insert_rc(&decl, &borrow_map);

    let s = format!("{:?}", result.body);
    // Verify RC operations exist (correctness: the call consumes x twice)
    assert!(
        s.contains("_inc"),
        "f(x, x) with owned params should generate inc for x: {s}"
    );
    // Note: clean generates 2 incs + 1 dec for this case (P3 over-increment).
    // Lean 4 optimal: 1 inc, 0 dec (isFirstOcc + numConsumptions-1 for dead var).
    // Both are correct — clean version has one extra inc/dec pair that cancels out.
}

// --- R2: last-use ownership transfer at consuming sites ---

/// Count `_inc`/`_dec` pseudo-ops naming `target` in the RC'd body.
fn count_rc_ops(code: &Code, op: &str, target: FVarId) -> usize {
    fn walk(code: &Code, op: &Name, target: FVarId, n: &mut usize) {
        match code {
            Code::Let(decl, rest) => {
                if let LetValue::Const { name, args, .. } = &decl.value {
                    if name == op && args.first() == Some(&Arg::FVar(target)) {
                        *n += 1;
                    }
                }
                walk(rest, op, target, n);
            }
            Code::Fun(f, rest) | Code::JoinPoint(f, rest) => {
                walk(&f.body, op, target, n);
                walk(rest, op, target, n);
            }
            Code::Cases(cases) => {
                for alt in &cases.alts {
                    walk(alt.body(), op, target, n);
                }
            }
            _ => {}
        }
    }
    let mut n = 0;
    walk(code, &Name::from_string(op), target, &mut n);
    n
}

fn rc_body(decl: &Decl) -> &Code {
    match &decl.body {
        crate::lcnf::DeclValue::Code(code) => code,
        other => panic!("expected code body, got {other:?}"),
    }
}

/// THE R2 LEAK PIN: a non-param local whose LAST use is a consuming call
/// transfers its ownership — no compensating inc, and no death dec. The
/// pre-R2 layout inc'd it unconditionally, and since a live-at-binding
/// local has no death dec anywhere (locals only dec at their binding when
/// DEAD; only params dec at return), one reference leaked per call —
/// `List.recOn`'s synthesized `go` leaked exactly one cons cell per step.
#[test]
fn test_local_last_use_at_call_transfers_no_inc_no_dec() {
    // def h (p) := let a := g(p); let r := g2(a); return r
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("a"),
            nat_type(),
            LetValue::Const {
                name: name("g"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("r"),
                nat_type(),
                LetValue::Const {
                    name: name("g2"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );
    let decl = Decl::new(
        name("h"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("p"), nat_type())],
        code,
        false,
    );
    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);
    let body = rc_body(&result);

    assert_eq!(
        count_rc_ops(body, "_inc", fvar(1)),
        0,
        "local `a`'s last use transfers — no compensating inc: {result}"
    );
    assert_eq!(
        count_rc_ops(body, "_dec", fvar(1)),
        0,
        "transferred local `a` must have no death dec either: {result}"
    );
    // The param p is still inc'd at its consuming use (its death dec sits at
    // the return), keeping the param discipline balanced.
    assert_eq!(
        count_rc_ops(body, "_inc", fvar(0)),
        1,
        "param inc: {result}"
    );
    assert_eq!(
        count_rc_ops(body, "_dec", fvar(0)),
        1,
        "param dec: {result}"
    );
}

/// Constructor stores are consuming sites too, and the args must be LIVE
/// above the allocation: pre-R2 the Ctor arm never marked its args live, so
/// a local consumed only by a ctor was dec'd at its own binding — BEFORE
/// the store that consumed it (use-after-free ordering) — while the
/// unconditional ctor inc leaked the reference the dec retired.
#[test]
fn test_local_last_use_at_ctor_transfers_and_stays_live_above() {
    // def f (p) := let a := g(p); let v := Box.mk a; return v
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("a"),
            nat_type(),
            LetValue::Const {
                name: name("g"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("v"),
                nat_type(),
                LetValue::Ctor {
                    name: name("Box.mk"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );
    let decl = Decl::new(
        name("f"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("p"), nat_type())],
        code,
        false,
    );
    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);
    let body = rc_body(&result);

    assert_eq!(
        count_rc_ops(body, "_inc", fvar(1)),
        0,
        "ctor consumes `a`'s last use — ownership transfers: {result}"
    );
    assert_eq!(
        count_rc_ops(body, "_dec", fvar(1)),
        0,
        "no death dec for `a` — and in particular no dec ABOVE the store \
         that consumes it: {result}"
    );
}

/// A local that stays LIVE after a consuming use keeps the compensating inc
/// (the consumer takes the inc'd reference), and its true last use — here a
/// constructor store — transfers.
#[test]
fn test_local_live_after_consuming_use_keeps_inc() {
    // def k (p) := let a := g(p); let r := g2(a); let v := Box.mk a r; return v
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("a"),
            nat_type(),
            LetValue::Const {
                name: name("g"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("r"),
                nat_type(),
                LetValue::Const {
                    name: name("g2"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1))],
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    fvar(3),
                    name("v"),
                    nat_type(),
                    LetValue::Ctor {
                        name: name("Box.mk"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
                    },
                ),
                Code::ret(fvar(3)),
            ),
        ),
    );
    let decl = Decl::new(
        name("k"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("p"), nat_type())],
        code,
        false,
    );
    let borrow_map = infer_borrow(std::slice::from_ref(&decl));
    let result = insert_rc(&decl, &borrow_map);
    let body = rc_body(&result);

    // `a`: inc'd once (live across the g2 call), then transferred at the
    // ctor. Born 1 (+1 inc, -1 g2, -1 store) = 0 — balanced with no dec.
    assert_eq!(count_rc_ops(body, "_inc", fvar(1)), 1, "{result}");
    assert_eq!(count_rc_ops(body, "_dec", fvar(1)), 0, "{result}");
    // `r`: last use is the store — transferred outright.
    assert_eq!(count_rc_ops(body, "_inc", fvar(2)), 0, "{result}");
    assert_eq!(count_rc_ops(body, "_dec", fvar(2)), 0, "{result}");
}

/// Duplicate occurrences of a dead-after local in ONE consuming site: only
/// one occurrence transfers; the rest are separate consumptions and keep
/// their incs. `f(a, a)` with `a` dead after = 1 transfer + 1 inc.
#[test]
fn test_duplicate_local_occurrence_transfers_once() {
    // def d (p) := let a := g(p); let r := f(a, a); return r
    let code = Code::let_bind(
        LetDecl::new(
            fvar(1),
            name("a"),
            nat_type(),
            LetValue::Const {
                name: name("g"),
                levels: vec![],
                args: vec![Arg::FVar(fvar(0))],
            },
        ),
        Code::let_bind(
            LetDecl::new(
                fvar(2),
                name("r"),
                nat_type(),
                LetValue::Const {
                    name: name("f"),
                    levels: vec![],
                    args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(1))],
                },
            ),
            Code::ret(fvar(2)),
        ),
    );
    let decl = Decl::new(
        name("d"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(0), name("p"), nat_type())],
        code,
        false,
    );
    let mut borrow_map = infer_borrow(std::slice::from_ref(&decl));
    borrow_map.insert(
        name("f"),
        crate::rc::borrow::FnBorrow {
            params: vec![Ownership::Owned, Ownership::Owned],
        },
    );
    let result = insert_rc(&decl, &borrow_map);
    let body = rc_body(&result);

    // Two owned consumptions of one owned reference: one transfer + one inc.
    assert_eq!(count_rc_ops(body, "_inc", fvar(1)), 1, "{result}");
    assert_eq!(count_rc_ops(body, "_dec", fvar(1)), 0, "{result}");
}
