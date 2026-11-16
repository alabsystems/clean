// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! WS5.12 — Clean `let` gets its kernel-TV companion (F-097, the `let` half).
//!
//! The rule itself is WS6.6's: `denote_source` zeta-substitutes a source
//! `let x : UIntW := v; b`. Before it the proof program's p03 `sqLet`
//! (`let t := a + 1; t * t`) was refused on the SOURCE side ("source construct
//! let …") while its emitted body (`add; mul; ret`) was in-fragment, and in
//! the ~/trust clean-origin island the missing kernel-TV companion was a FATAL
//! evidence disagreement. This file pins what WS5.12's Tests field asks of
//! that rule at the reflect level, against the kernel:
//!
//! * positive: the ELABORATOR-shaped `Let` (`HAdd.hAdd`/`HMul.hMul`
//!   dispatchers, `OfNat.ofNat` literal — what `elab_let` builds) denotes
//!   IDENTICALLY to the shared SSA, single and nested, and the kernel accepts
//!   the equation; the environment walk agrees with the kernel's own zeta
//!   (`Expr::instantiate`) on every shape here;
//! * negative twin: a `let` whose bound value is an op the fragment rejects
//!   (a non-wrapping `HDiv.hDiv`) stays refused with its EXISTING class — the
//!   refusal names the op, never the `let`;
//! * mutation control: zeta with the WRONG de Bruijn shift (indices above the
//!   let binder left un-lowered) is in scope, so it DENOTES — and the kernel
//!   REFUSES the equation, so a wrong shift can never publish a row;
//! * risk pin: the `letFun` application spelling of a `let` is NOT handled
//!   (the compiler-side positive measures that p03 elaborates to `Let`) and
//!   is refused naming `letFun`, never through the zeta arm;
//! * scope pin: the Fragment-5 `Nat` floor is untouched (a `let` there is
//!   still refused by name).

use super::*;
use clean_kernel::{BinderInfo, Declaration, Environment};
use trust_ir::{BlockId, FuncId, FuncTy, FuncTyId, Function, InstrNode, ValueId};

/// `UInt<W>` — the fixture width. p03 is `UInt64`; the mutation control runs
/// at `UInt32` because a kernel REFUSAL at width 64 costs ~100 s (the kernel
/// keeps unfolding `Nat.mod _ 2^64` before it gives up) and the de Bruijn
/// point is width-independent.
fn uint(w: u32) -> Expr {
    Expr::const_str(&format!("UInt{w}"))
}

/// The elaborator-shaped literal `OfNat.ofNat UInt<W> k inst`.
fn of_nat(w: u32, k: u64) -> Expr {
    Expr::apps(
        Expr::const_str("OfNat.ofNat"),
        [
            uint(w),
            Expr::nat_lit(k),
            Expr::apps(
                Expr::const_str("OfNat.mk"),
                [
                    uint(w),
                    Expr::nat_lit(k),
                    Expr::app(Expr::const_str(&format!("UInt{w}.ofNat")), Expr::nat_lit(k)),
                ],
            ),
        ],
    )
}

/// The elaborator-shaped `H<Op>.h<op> UInt<W> UInt<W> UInt<W> inst a b`.
fn hop(w: u32, class: &str, method: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str(&format!("{class}.{method}")),
        [
            uint(w),
            uint(w),
            uint(w),
            Expr::apps(
                Expr::const_str(&format!("{class}.mk")),
                [
                    uint(w),
                    uint(w),
                    uint(w),
                    Expr::const_str(&format!(
                        "UInt{w}.{}",
                        method.trim_start_matches('h').to_ascii_lowercase()
                    )),
                ],
            ),
            a,
            b,
        ],
    )
}

fn hadd(w: u32, a: Expr, b: Expr) -> Expr {
    hop(w, "HAdd", "hAdd", a, b)
}

fn hmul(w: u32, a: Expr, b: Expr) -> Expr {
    hop(w, "HMul", "hMul", a, b)
}

fn hsub(w: u32, a: Expr, b: Expr) -> Expr {
    hop(w, "HSub", "hSub", a, b)
}

fn hdiv(w: u32, a: Expr, b: Expr) -> Expr {
    hop(w, "HDiv", "hDiv", a, b)
}

/// `let t : UInt<W> := value; body` exactly as `elab_let` builds it
/// (`Expr::let_named(name, ty, val, body_abs, false)`).
fn let_w(w: u32, name: &str, value: Expr, body: Expr) -> Expr {
    Expr::let_named(Name::from_string(name), uint(w), value, body, false)
}

/// `fun (x_0 … x_{n-1} : UInt<W>) => body`.
fn lam_n(w: u32, n: usize, body: Expr) -> Expr {
    (0..n).fold(body, |acc, _| Expr::lam(BinderInfo::Default, uint(w), acc))
}

fn denote_src(w: u32, defn: &Expr) -> Result<TvDenotation, ReflectError> {
    denote_source(defn, w, &[], &RecordVocab::empty())
}

/// A straight-line `U<W>^n -> U<W>` emitted fixture builder.
struct Emit {
    ty: Ty,
    func: Function,
    block: trust_ir::Block,
    next: u32,
}

impl Emit {
    fn new(w: u32, params: usize) -> Self {
        let ty = match w {
            32 => Ty::U32,
            64 => Ty::U64,
            other => panic!("fixture width {other}"),
        };
        let func = Function::new(FuncId::new(0), "ws5_12", FuncTyId::new(0), BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        for i in 0..params {
            block.params.push((ValueId::new(i as u32), ty.clone()));
        }
        Emit {
            ty,
            func,
            block,
            next: params as u32,
        }
    }

    fn param(&self, i: u32) -> ValueId {
        ValueId::new(i)
    }

    fn konst(&mut self, k: i128) -> ValueId {
        let r = ValueId::new(self.next);
        self.next += 1;
        self.block.body.push(
            InstrNode::new(Inst::Const {
                ty: self.ty.clone(),
                value: Constant::Int(k),
            })
            .with_result(r),
        );
        r
    }

    fn bin(&mut self, op: BinOp, lhs: ValueId, rhs: ValueId) -> ValueId {
        let r = ValueId::new(self.next);
        self.next += 1;
        self.block.body.push(
            InstrNode::new(Inst::BinOp {
                op,
                ty: self.ty.clone(),
                lhs,
                rhs,
            })
            .with_result(r),
        );
        r
    }

    fn finish(mut self, ret: ValueId, params: usize) -> Module {
        self.block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![ret] }));
        self.func.blocks.push(self.block);
        let mut module = Module::new("ws5_12_fixture");
        module.func_types.push(FuncTy {
            params: vec![self.ty.clone(); params],
            returns: vec![self.ty.clone()],
            is_vararg: false,
            abi: None,
        });
        module
            .try_add_function(self.func)
            .expect("Module::try_add_function: test fixture");
        module
    }
}

/// The p03 emitted body at `-O1`/`-O2` (`emit_trust_ir_ws6_4_tests` pins it):
/// `c1 = const 1; t = add a c1; r = mul t t; ret r` — the SSA shares `t`.
fn sq_let_module() -> Module {
    let mut e = Emit::new(64, 1);
    let a = e.param(0);
    let c1 = e.konst(1);
    let t = e.bin(BinOp::Add, a, c1);
    let r = e.bin(BinOp::Mul, t, t);
    e.finish(r, 1)
}

/// p03 verbatim: `fun (a : UInt64) => let t := a + 1; t * t`. Inside the let
/// body `t` is `bvar 0` and `a` is `bvar 1`.
fn sq_let_source() -> Expr {
    lam_n(
        64,
        1,
        let_w(
            64,
            "t",
            hadd(64, Expr::bvar(0), of_nat(64, 1)),
            hmul(64, Expr::bvar(0), Expr::bvar(0)),
        ),
    )
}

/// Declare the TV theorem in a fresh prelude env; Ok iff the kernel ACCEPTS
/// the equation (the same `add_decl` gate the re-checker runs).
fn kernel_decides(
    arity: usize,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<(), clean_kernel::KernelEnvError> {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(&tv_theorem_name("ws5_12")),
        level_params: vec![],
        type_: tv_statement(&[], arity, lhs, rhs),
        value: tv_proof_term(&[], arity, lhs),
    })
}

#[test]
fn test_ws5_12_let_source_denotes_identically_to_shared_ssa() {
    // THE AGREEMENT: zeta duplicates the bound value in the source exactly as
    // the SSA shares it, so the two maps land on the SAME Expr.
    let module = sq_let_module();
    let lhs = denote_function(&module, &module.functions[0]).expect("emitted side in-fragment");
    let rhs = denote_src(64, &sq_let_source()).expect("a source `let` is zeta-reduced and denoted");
    assert_eq!(rhs.arity, 1);
    assert_eq!(rhs.width, 64);
    assert_eq!(
        lhs.body, rhs.body,
        "the let must denote to the shared-value expression"
    );

    let m = modulus(64);
    let t = Expr::apps(
        Expr::const_str("Nat.mod"),
        [
            Expr::apps(
                Expr::const_str("Nat.add"),
                [Expr::bvar(0), Expr::nat_lit(1)],
            ),
            m.clone(),
        ],
    );
    let expected = Expr::apps(
        Expr::const_str("Nat.mod"),
        [Expr::apps(Expr::const_str("Nat.mul"), [t.clone(), t]), m],
    );
    assert_eq!(rhs.body, expected);
}

#[test]
fn test_ws5_12_kernel_accepts_the_honest_let_equation() {
    let module = sq_let_module();
    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let rhs = denote_src(64, &sq_let_source()).unwrap();
    kernel_decides(lhs.arity, &lhs.body, &rhs.body)
        .expect("the kernel must decide the honest `let` equation");
}

#[test]
fn test_ws5_12_kernel_refuses_miscompiled_let_body() {
    // MISCOMPILE DETECTOR still armed through the zeta: emitted `(a+1)*(a+1)`
    // patched to `(a+1)+(a+1)` must be REFUSED against the `let` source.
    let mut module = sq_let_module();
    let Inst::BinOp { op, .. } = &mut module.functions[0].blocks[0].body[2].inst else {
        panic!("fixture layout: node 2 is the Mul");
    };
    *op = BinOp::Add;
    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let rhs = denote_src(64, &sq_let_source()).unwrap();
    assert!(
        kernel_decides(lhs.arity, &lhs.body, &rhs.body).is_err(),
        "the kernel must refuse: (a+1)+(a+1) does not denote (a+1)*(a+1)"
    );
}

/// `fun (a b : UInt64) => let t := a + 1; let u := t * b; u - a`: nested
/// lets, a value mentioning the OUTER parameter, a body mentioning the
/// inner let, the outer let and a parameter. Emitted: `t = add a 1;
/// u = mul t b; r = sub u a`.
fn nested_let_module() -> Module {
    let mut e = Emit::new(64, 2);
    let a = e.param(0);
    let b = e.param(1);
    let c1 = e.konst(1);
    let t = e.bin(BinOp::Add, a, c1);
    let u = e.bin(BinOp::Mul, t, b);
    let r = e.bin(BinOp::Sub, u, a);
    e.finish(r, 2)
}

fn nested_let_source() -> Expr {
    // Outer context: b = bvar 0, a = bvar 1.
    // Inside `let t`:  t = 0, b = 1, a = 2.
    // Inside `let u`:  u = 0, t = 1, b = 2, a = 3.
    lam_n(
        64,
        2,
        let_w(
            64,
            "t",
            hadd(64, Expr::bvar(1), of_nat(64, 1)),
            let_w(
                64,
                "u",
                hmul(64, Expr::bvar(0), Expr::bvar(1)),
                hsub(64, Expr::bvar(0), Expr::bvar(3)),
            ),
        ),
    )
}

#[test]
fn test_ws5_12_nested_lets_denote_identically_and_kernel_accepts() {
    let module = nested_let_module();
    let lhs = denote_function(&module, &module.functions[0]).expect("emitted side in-fragment");
    let rhs = denote_src(64, &nested_let_source()).expect("nested lets zeta-reduce in order");
    assert_eq!(rhs.arity, 2);
    assert_eq!(
        lhs.body, rhs.body,
        "each zeta must lift the value under the binders it crosses and lower the rest"
    );
    kernel_decides(lhs.arity, &lhs.body, &rhs.body)
        .expect("the kernel must decide the honest nested-let equation");
}

#[test]
fn test_ws5_12_environment_walk_agrees_with_kernel_zeta() {
    // TWO FORMULATIONS AGREE: the denoter's let ENVIRONMENT (WS6.6) and the
    // kernel's own capture-avoiding `Expr::instantiate` (the zeta the roadmap
    // names) must produce the same comparand — for the single let, the
    // nested lets, and a let whose value is itself a let.
    let single = sq_let_source();
    let single_reduct = {
        let ExprKind::Lam(_, _, body) = single.kind() else {
            unreachable!()
        };
        let ExprKind::Let(_, _, v, b, _) = body.kind() else {
            unreachable!()
        };
        lam_n(64, 1, b.instantiate(v))
    };
    assert_eq!(
        denote_src(64, &single).unwrap().body,
        denote_src(64, &single_reduct).unwrap().body
    );

    let nested = nested_let_source();
    let nested_reduct = {
        let ExprKind::Lam(_, _, b1) = nested.kind() else {
            unreachable!()
        };
        let ExprKind::Lam(_, _, body) = b1.kind() else {
            unreachable!()
        };
        let ExprKind::Let(_, _, v, b, _) = body.kind() else {
            unreachable!()
        };
        let once = b.instantiate(v);
        let ExprKind::Let(_, _, v2, b2, _) = once.kind() else {
            unreachable!()
        };
        lam_n(64, 2, b2.instantiate(v2))
    };
    assert_eq!(
        denote_src(64, &nested).unwrap().body,
        denote_src(64, &nested_reduct).unwrap().body
    );

    // `fun a => let t := (let s := a + 1; s * s); t - a`: a let in VALUE
    // position, so the environment must be extended while walking a value.
    let inner = let_w(
        64,
        "s",
        hadd(64, Expr::bvar(0), of_nat(64, 1)),
        hmul(64, Expr::bvar(0), Expr::bvar(0)),
    );
    let value_let = lam_n(
        64,
        1,
        let_w(
            64,
            "t",
            inner.clone(),
            hsub(64, Expr::bvar(0), Expr::bvar(1)),
        ),
    );
    let ExprKind::Let(_, _, sv, sb, _) = inner.kind() else {
        unreachable!()
    };
    let value_reduct = lam_n(64, 1, hsub(64, sb.instantiate(sv), Expr::bvar(0)));
    let den = denote_src(64, &value_let).expect("a let in value position denotes");
    assert_eq!(den.body, denote_src(64, &value_reduct).unwrap().body);
    let mut e = Emit::new(64, 1);
    let a = e.param(0);
    let c1 = e.konst(1);
    let s = e.bin(BinOp::Add, a, c1);
    let t = e.bin(BinOp::Mul, s, s);
    let r = e.bin(BinOp::Sub, t, a);
    let module = e.finish(r, 1);
    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    kernel_decides(1, &lhs.body, &den.body).expect("the kernel decides the value-let equation");
}

#[test]
fn test_ws5_12_let_bound_out_of_fragment_op_stays_refused_by_its_op() {
    // NEGATIVE TWIN: `let t := a / 2; t * t`. Division is not a wrapping op
    // the fragment denotes; zeta must not launder it. The refusal is the
    // EXISTING class — `Unsupported`, naming `HDiv.hDiv` — and never blames
    // the `let`, so the reason a consumer reads is the real one.
    let defn = lam_n(
        64,
        1,
        let_w(
            64,
            "t",
            hdiv(64, Expr::bvar(0), of_nat(64, 2)),
            hmul(64, Expr::bvar(0), Expr::bvar(0)),
        ),
    );
    let err =
        denote_src(64, &defn).expect_err("a let-bound division is out of the source fragment");
    assert!(
        matches!(err, ReflectError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("headed by `HDiv.hDiv`"),
        "the refusal must name the op: {msg}"
    );
    assert!(
        !msg.contains("source construct let"),
        "the pre-WS5.12 `let` refusal must be gone: {msg}"
    );
}

#[test]
fn test_ws5_12_let_body_escaping_the_telescope_stays_refused() {
    // A let body reaching past the parameter telescope THROUGH the let
    // (`bvar 2` under one param and one let binder) is still the escaping
    // bvar refusal — one let is accounted for, one parameter, nothing else.
    let defn = lam_n(64, 1, let_w(64, "t", of_nat(64, 1), Expr::bvar(2)));
    let err = denote_src(64, &defn).expect_err("an escaping bvar under a let must fail closed");
    assert!(matches!(err, ReflectError::Unsupported { .. }));
    let msg = err.to_string();
    assert!(
        msg.contains("escaping the 1-parameter telescope"),
        "got {msg}"
    );
}

/// Zeta with the WRONG de Bruijn shift for the mutation-control body
/// `mul (bvar 0) (bvar 1)`: `bvar 0` is replaced by the value, but the index
/// above the let binder is left where it was (`bvar 1`) instead of being
/// lowered to `bvar 0`. Spelled out by hand because the kernel's own
/// substitution cannot be asked to get this wrong.
fn wrong_shift_zeta(value: &Expr) -> Expr {
    hmul(32, value.clone(), Expr::bvar(1))
}

#[test]
fn test_ws5_12_mutation_wrong_de_bruijn_shift_is_refused_by_the_kernel() {
    // MUTATION CONTROL (at `UInt32`, see [`uint`]): `fun (a b) => let t :=
    // a + 1; t * b`, emitted `t = add a 1; r = mul t b`. Inside the let body
    // `t = bvar 0`, `b = bvar 1`, `a = bvar 2`; the value in the outer
    // context is `bvar 1 + 1`.
    //   correct zeta: `(bvar 1 + 1) * bvar 0`  = (a + 1) * b
    //   wrong shift : `(bvar 1 + 1) * bvar 1`  = (a + 1) * a
    // Both are in scope (every index < 2), so the wrong reduct DENOTES — and
    // the kernel is what refuses it. A wrong shift can therefore never
    // publish a row: the certificate is re-checked by the kernel, not taken
    // on faith from the denoter.
    let mut e = Emit::new(32, 2);
    let a = e.param(0);
    let b = e.param(1);
    let c1 = e.konst(1);
    let t = e.bin(BinOp::Add, a, c1);
    let r = e.bin(BinOp::Mul, t, b);
    let module = e.finish(r, 2);
    let lhs = denote_function(&module, &module.functions[0]).unwrap();

    let value = hadd(32, Expr::bvar(1), of_nat(32, 1));
    let body = hmul(32, Expr::bvar(0), Expr::bvar(1));
    let honest = lam_n(32, 2, let_w(32, "t", value.clone(), body.clone()));
    let rhs = denote_src(32, &honest).unwrap();
    assert_eq!(lhs.body, rhs.body);
    kernel_decides(2, &lhs.body, &rhs.body).expect("the honest equation is accepted");

    // The correct reduct is what the production walk denotes …
    let correct = lam_n(32, 2, body.instantiate(&value));
    assert_eq!(denote_src(32, &correct).unwrap().body, rhs.body);

    // … and the mutant is a different, in-scope function the kernel refuses.
    let mutant_reduct = wrong_shift_zeta(&value);
    assert_eq!(
        body.instantiate(&value),
        hmul(32, value.clone(), Expr::bvar(0)),
        "the kernel's zeta lowers the parameter index past the let binder"
    );
    assert_ne!(mutant_reduct, body.instantiate(&value));
    let mutant = lam_n(32, 2, mutant_reduct);
    let wrong = denote_src(32, &mutant)
        .expect("the wrong reduct is in scope, so it denotes — the kernel must catch it");
    assert_ne!(
        lhs.body, wrong.body,
        "the wrong shift denotes a different function"
    );
    assert!(
        kernel_decides(2, &lhs.body, &wrong.body).is_err(),
        "the kernel must refuse: (a+1)*a does not denote (a+1)*b"
    );
}

#[test]
fn test_ws5_12_let_fun_spelling_is_refused_by_name() {
    // RISK LINE (roadmap WS5.12): a `let` body "may be elaborated with
    // `have`/`letFun` rather than `Let`. Handle it only if measured, and
    // otherwise refuse by name." The compiler-side positive
    // (`emit_trust_ir::tests::ws5_12::gap_a_lean_let_emit_flips`) MEASURES
    // that Clean's elaborator builds `ExprKind::Let` for p03, so the
    // application spelling `letFun α (fun _ => β) v (fun t => b)` is NOT
    // handled — and it must not be laundered through the zeta arm. It is an
    // application headed by the constant `letFun`, which the fragment refuses
    // NAMING that head, never as a `let`.
    let let_fun = Expr::apps(
        Expr::const_str("letFun"),
        [
            uint(64),
            Expr::lam(BinderInfo::Default, uint(64), uint(64)),
            hadd(64, Expr::bvar(0), of_nat(64, 1)),
            Expr::lam(
                BinderInfo::Default,
                uint(64),
                hmul(64, Expr::bvar(0), Expr::bvar(0)),
            ),
        ],
    );
    let defn = lam_n(64, 1, let_fun);
    let err = denote_src(64, &defn).expect_err("a `letFun` spelling is out of the source fragment");
    assert!(matches!(err, ReflectError::Unsupported { .. }));
    let msg = err.to_string();
    assert!(
        msg.contains("headed by `letFun`"),
        "the refusal must name `letFun`: {msg}"
    );
    assert!(
        !msg.contains("source let binding"),
        "the `Let` arm must not have claimed it: {msg}"
    );
}

#[test]
fn test_ws5_12_nat_floor_still_refuses_let_by_name() {
    // SCOPE PIN: the `let` rule widens the UIntW source fragment only. The
    // Fragment-5 parameter-free `Nat` floor has no zeta arm; a `let` there is
    // refused fail-closed with the head-is-not-a-constant label, unchanged.
    let defn = Expr::let_named(
        Name::from_string("k"),
        Expr::const_str("Nat"),
        Expr::nat_lit(5),
        Expr::bvar(0),
        false,
    );
    let err = denote_source_nat(&defn, &[]).expect_err("a Nat-floor let is out of fragment");
    assert!(matches!(err, ReflectError::Unsupported { .. }));
    assert!(
        err.to_string()
            .contains("head is not a recognized constant"),
        "got {err}"
    );
}

// --- Review (adversarial) ---------------------------------------------------
//
// Inputs the increment did not write, each aimed at one way the `let` rule
// could accept a false claim or refuse a legitimate module: a let at the
// WRONG width, an unused out-of-fragment value the emitted side has already
// dropped, a let in ARGUMENT position and an alias chain, and a let inside a
// conditional whose value crosses into both arms.

#[test]
fn test_ws5_12_review_let_at_another_width_is_refused_naming_the_type() {
    // `fun (a : UInt64) => let t : UInt32 := 1; a`. The bound value would be
    // denoted as a U-64 value while the binder says U-32 — a wrap-width lie
    // the zeta arm must not launder even though the body never uses `t`.
    let defn = lam_n(
        64,
        1,
        Expr::let_named(
            Name::from_string("t"),
            uint(32),
            of_nat(32, 1),
            Expr::bvar(1),
            false,
        ),
    );
    let err = denote_src(64, &defn).expect_err("a let at another width is out of fragment");
    assert!(matches!(err, ReflectError::Unsupported { .. }));
    let msg = err.to_string();
    assert!(
        msg.contains("source let binding at type UInt32") && msg.contains("must bind a UInt64"),
        "the refusal names the binder type and the fragment width: {msg}"
    );
}

#[test]
fn test_ws5_12_review_unused_out_of_fragment_value_is_refused_eagerly() {
    // `fun a => let t := a / 2; a + 1`: the emitted side at `-O1`/`-O2` has
    // DCE'd the division and IS in-fragment (`add a 1; ret`), so the ONLY
    // thing standing between this source and a certificate is the eager
    // value denotation. It must refuse, naming the division — the roadmap's
    // negative twin in its literal "bound value is unused" form.
    let mut e = Emit::new(64, 1);
    let a = e.param(0);
    let c1 = e.konst(1);
    let r = e.bin(BinOp::Add, a, c1);
    let module = e.finish(r, 1);
    denote_function(&module, &module.functions[0])
        .expect("the emitted side (division dropped) is in-fragment");

    let defn = lam_n(
        64,
        1,
        let_w(
            64,
            "t",
            hdiv(64, Expr::bvar(0), of_nat(64, 2)),
            hadd(64, Expr::bvar(1), of_nat(64, 1)),
        ),
    );
    let err = denote_src(64, &defn).expect_err("an unused out-of-fragment let value still refuses");
    assert!(matches!(err, ReflectError::Unsupported { .. }));
    let msg = err.to_string();
    assert!(msg.contains("headed by `HDiv.hDiv`"), "got {msg}");
    assert!(!msg.contains("let binding"), "got {msg}");
}

#[test]
fn test_ws5_12_review_let_in_argument_position_and_alias_chain() {
    // `fun a => a * (let t := a + 1; t)`: the let is an OPERAND of the
    // enclosing binop, so the environment is extended mid-argument and must
    // not leak into the sibling operand. Emitted: `t = add a 1; r = mul a t`.
    let mut e = Emit::new(64, 1);
    let a = e.param(0);
    let c1 = e.konst(1);
    let t = e.bin(BinOp::Add, a, c1);
    let r = e.bin(BinOp::Mul, a, t);
    let module = e.finish(r, 1);
    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let defn = lam_n(
        64,
        1,
        hmul(
            64,
            Expr::bvar(0),
            let_w(
                64,
                "t",
                hadd(64, Expr::bvar(0), of_nat(64, 1)),
                Expr::bvar(0),
            ),
        ),
    );
    let rhs = denote_src(64, &defn).expect("a let in argument position denotes");
    assert_eq!(lhs.body, rhs.body);
    kernel_decides(1, &lhs.body, &rhs.body).expect("the kernel decides the operand-let equation");

    // `fun a => let t := a; let u := t; u * u`: an alias chain through two
    // lets, each a bare bvar, must resolve to the PARAMETER (`a * a`), not to
    // a stale let index. Emitted: `r = mul a a`.
    let mut e = Emit::new(64, 1);
    let a = e.param(0);
    let r = e.bin(BinOp::Mul, a, a);
    let module = e.finish(r, 1);
    let lhs = denote_function(&module, &module.functions[0]).unwrap();
    let defn = lam_n(
        64,
        1,
        let_w(
            64,
            "t",
            Expr::bvar(0),
            let_w(
                64,
                "u",
                Expr::bvar(0),
                hmul(64, Expr::bvar(0), Expr::bvar(0)),
            ),
        ),
    );
    let rhs = denote_src(64, &defn).expect("an alias chain denotes");
    assert_eq!(lhs.body, rhs.body, "both aliases resolve to the parameter");
    kernel_decides(1, &lhs.body, &rhs.body).expect("the kernel decides the alias equation");
}

#[test]
fn test_ws5_12_review_let_value_crosses_into_both_conditional_arms() {
    // `fun a => let t := a + 1; cond (a < 5) t (t * t)`: the environment is
    // threaded through the Fragment-3a condition and BOTH arms. Checked
    // against the kernel's own zeta (`instantiate`), the formulation the
    // roadmap names, so a dropped environment on either arm is caught even
    // without an emitted twin.
    let value = hadd(64, Expr::bvar(0), of_nat(64, 1));
    let body = Expr::apps(
        Expr::const_str("cond"),
        [
            uint(64),
            Expr::apps(
                Expr::const_str("UInt64.blt"),
                [Expr::bvar(1), of_nat(64, 5)],
            ),
            Expr::bvar(0),
            hmul(64, Expr::bvar(0), Expr::bvar(0)),
        ],
    );
    let defn = lam_n(64, 1, let_w(64, "t", value.clone(), body.clone()));
    let den = denote_src(64, &defn).expect("a let over a conditional denotes");
    let reduct = lam_n(64, 1, body.instantiate(&value));
    assert_eq!(den.body, denote_src(64, &reduct).unwrap().body);
    // And the value really reached both arms: the reduct's else arm is the
    // squared sum, so a walk that dropped the environment on one arm would
    // have failed closed ("escaping the telescope") or produced `a`.
    let m = modulus(64);
    let t = Expr::apps(
        Expr::const_str("Nat.mod"),
        [
            Expr::apps(
                Expr::const_str("Nat.add"),
                [Expr::bvar(0), Expr::nat_lit(1)],
            ),
            m.clone(),
        ],
    );
    let sq = Expr::apps(
        Expr::const_str("Nat.mod"),
        [
            Expr::apps(Expr::const_str("Nat.mul"), [t.clone(), t.clone()]),
            m,
        ],
    );
    let cond = Expr::apps(
        Expr::const_str("Nat.blt"),
        [Expr::bvar(0), Expr::nat_lit(5)],
    );
    assert_eq!(den.body, ite_nat(cond, t, sq));
}
