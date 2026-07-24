// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FAIL-CLOSED kernel-diversity gate (FRONTIER 3 / #97 increment #3).
//!
//! This test is the deliverable described in the task: for a REAL `:= rfl`
//! corpus (the AArch64 64-bit/32-bit integer B-def op theorems, mirroring
//! `proofs/aarch64_isa.lean`), it runs each theorem through
//!
//! ```text
//! kernel infer-with-cert  ->  CertVerifier replay  ->  env-aware MICRO re-check
//! ```
//!
//! and FAILS CLOSED on any micro `Unsupported` or disagreement over the
//! TARGETED decls. The micro re-check is the genuinely-independent second
//! checker: it resolves `Const`s via a read-only [`MicroEnv`] (DELTA) and
//! re-derives the `lhs ≡ rhs` reduction with its OWN native Nat reducer
//! (IOTA) — it never calls the kernel's `whnf`/`is_def_eq`.
//!
//! NON-VACUITY is proven by sibling tests:
//!  * a deliberately-FALSE rfl theorem makes the gate FAIL (Disagreement),
//!  * a decl using a recursor the micro env cannot model (`bvAsr`, which uses
//!    `Bool`/`ite`) is reported `Unsupported` and FAILS CLOSED — not skipped.

use clean_kernel::cert::CertVerifier;
use clean_kernel::env::Declaration;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::micro::{diversity_check_rfl, DiversityOutcome, MicroEnv};
use clean_kernel::name::Name;
use clean_kernel::Environment;

// ---------------------------------------------------------------------------
// Corpus construction: register the AArch64 B-defs (mirroring aarch64_isa.lean)
// as reducible Definitions in a real kernel Environment, plus their `:= rfl`
// boundary theorems with pure `@Eq.refl Nat <lhs>` proof terms.
// ---------------------------------------------------------------------------

fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}

/// 2-ary Nat def: `λ a b => <body(a=bvar1, b=bvar0)>`, registered reducible.
fn def2(env: &mut Environment, name: &str, body: Expr) {
    let nat = c("Nat");
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), body),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}

/// 1-ary Nat def.
fn def1(env: &mut Environment, name: &str, body: Expr) {
    let nat = c("Nat");
    let ty = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
    let value = Expr::lam(BinderInfo::Default, nat.clone(), body);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}

/// 0-ary Nat constant def.
fn def0(env: &mut Environment, name: &str, body: Expr) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: c("Nat"),
        value: body,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.add"), [a, b])
}
fn nat_sub(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.sub"), [a, b])
}
fn nat_mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.mul"), [a, b])
}
fn nat_mod(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.mod"), [a, b])
}
fn nat_pow(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.pow"), [a, b])
}
fn nat_land(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.land"), [a, b])
}
fn nat_lor(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.lor"), [a, b])
}
fn nat_xor(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.xor"), [a, b])
}
fn nat_shl(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.shiftLeft"), [a, b])
}
fn nat_shr(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.shiftRight"), [a, b])
}
fn lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn bvar(i: u32) -> Expr {
    Expr::bvar(i)
}
fn nat_beq(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.beq"), [a, b])
}
fn nat_ble(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.ble"), [a, b])
}

// ---- Bool layer (the increment-2 additions) -------------------------------
// `if (c : Bool) then t else e` desugars to `cond`, which the kernel reduces
// through `Bool.rec`. We mirror that VERBATIM as the explicit recursor app
// `@Bool.rec.{1} (fun _ => <ty>) <else> <then> <c>` (minor order: false-case,
// true-case) — exactly the form the prelude's `Bool.not`/`Bool.and`/`cond` take
// and the form the new micro `Bool.rec` IOTA reduces.
fn bool_true() -> Expr {
    c("Bool.true")
}
fn bool_false() -> Expr {
    c("Bool.false")
}
/// `Bool.and a b` (prelude reducible def -> `Bool.rec`).
fn bool_and(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Bool.and"), [a, b])
}
/// `Bool.not a` (prelude reducible def -> `Bool.rec`).
fn bool_not(a: Expr) -> Expr {
    Expr::app(c("Bool.not"), a)
}
/// `Bool.beq a b` (boolean equality; prelude reducible def, native in micro).
fn bool_beq(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Bool.beq"), [a, b])
}
/// `if (cond : Bool) then then_ else else_` at result type `elem_ty`, mirrored
/// as `@Bool.rec.{1} (fun _ : Bool => elem_ty) else_ then_ cond`.
fn cond_at(elem_ty: Expr, cond: Expr, then_: Expr, else_: Expr) -> Expr {
    let type1 = Level::succ(Level::zero());
    let motive = Expr::lam(BinderInfo::Default, c("Bool"), elem_ty);
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![type1]),
        [motive, else_, then_, cond],
    )
}

/// 2-ary `Nat -> Nat -> Bool` def, registered reducible.
fn def2_bool(env: &mut Environment, name: &str, body: Expr) {
    let nat = c("Nat");
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), c("Bool")),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), body),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}

/// 1-ary `Nat -> Bool` def, registered reducible.
fn def1_bool(env: &mut Environment, name: &str, body: Expr) {
    let nat = c("Nat");
    let ty = Expr::pi(BinderInfo::Default, nat.clone(), c("Bool"));
    let value = Expr::lam(BinderInfo::Default, nat.clone(), body);
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("register {name}: {e}"));
}

/// Build the corpus environment. Returns the kernel env with all B-defs
/// registered. Mirrors `proofs/aarch64_isa.lean` def bodies exactly.
fn build_corpus_env() -> Environment {
    let mut env = Environment::with_prelude();
    let nat = c("Nat");
    let a = || bvar(1);
    let b = || bvar(0);

    // Word sizes.
    def0(&mut env, "AArch64.W", nat_pow(lit(2), lit(64)));
    def0(&mut env, "AArch64.SignBit", nat_pow(lit(2), lit(63)));
    def0(&mut env, "AArch64.AllOnes", nat_sub(c("AArch64.W"), lit(1)));
    def0(&mut env, "AArch64.Ww", nat_pow(lit(2), lit(32)));
    def0(&mut env, "AArch64.SignBitW", nat_pow(lit(2), lit(31)));
    def0(
        &mut env,
        "AArch64.AllOnesW",
        nat_sub(c("AArch64.Ww"), lit(1)),
    );

    // canon a := a % W
    def1(&mut env, "AArch64.canon", nat_mod(bvar(0), c("AArch64.W")));

    // Arithmetic.
    def2(
        &mut env,
        "AArch64.bvAdd",
        nat_mod(nat_add(a(), b()), c("AArch64.W")),
    );
    def2(
        &mut env,
        "AArch64.bvSub",
        nat_mod(
            nat_add(a(), nat_sub(c("AArch64.W"), nat_mod(b(), c("AArch64.W")))),
            c("AArch64.W"),
        ),
    );
    def2(
        &mut env,
        "AArch64.bvMul",
        nat_mod(nat_mul(a(), b()), c("AArch64.W")),
    );
    // bvNeg a := bvSub 0 a
    def1(
        &mut env,
        "AArch64.bvNeg",
        Expr::apps(c("AArch64.bvSub"), [lit(0), bvar(0)]),
    );

    // Bitwise.
    def2(&mut env, "AArch64.bvAnd", nat_land(a(), b()));
    def2(&mut env, "AArch64.bvOr", nat_lor(a(), b()));
    def2(&mut env, "AArch64.bvXor", nat_xor(a(), b()));
    // bvNot a := (a % W) XOR AllOnes
    def1(
        &mut env,
        "AArch64.bvNot",
        nat_xor(nat_mod(bvar(0), c("AArch64.W")), c("AArch64.AllOnes")),
    );
    // bvBic a b := a AND (bvNot b)
    def2(
        &mut env,
        "AArch64.bvBic",
        nat_land(a(), Expr::app(c("AArch64.bvNot"), b())),
    );
    // bvOrn a b := a OR (bvNot b)
    def2(
        &mut env,
        "AArch64.bvOrn",
        nat_lor(a(), Expr::app(c("AArch64.bvNot"), b())),
    );

    // Shifts (amount masked &63).
    def2(
        &mut env,
        "AArch64.bvShl",
        nat_mod(nat_shl(a(), nat_mod(b(), lit(64))), c("AArch64.W")),
    );
    def2(
        &mut env,
        "AArch64.bvLshr",
        nat_shr(nat_mod(a(), c("AArch64.W")), nat_mod(b(), lit(64))),
    );

    // 32-bit W-forms.
    def2(
        &mut env,
        "AArch64.bvAddW",
        nat_mod(
            nat_add(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
            c("AArch64.Ww"),
        ),
    );
    def2(
        &mut env,
        "AArch64.bvSubW",
        nat_mod(
            nat_add(
                nat_mod(a(), c("AArch64.Ww")),
                nat_sub(c("AArch64.Ww"), nat_mod(b(), c("AArch64.Ww"))),
            ),
            c("AArch64.Ww"),
        ),
    );
    def2(
        &mut env,
        "AArch64.bvMulW",
        nat_mod(
            nat_mul(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
            c("AArch64.Ww"),
        ),
    );
    def1(
        &mut env,
        "AArch64.bvNegW",
        Expr::apps(c("AArch64.bvSubW"), [lit(0), bvar(0)]),
    );
    def2(
        &mut env,
        "AArch64.bvAndW",
        nat_land(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
    );
    def2(
        &mut env,
        "AArch64.bvOrW",
        nat_lor(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
    );
    def2(
        &mut env,
        "AArch64.bvXorW",
        nat_xor(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
    );
    def1(
        &mut env,
        "AArch64.bvNotW",
        nat_xor(nat_mod(bvar(0), c("AArch64.Ww")), c("AArch64.AllOnesW")),
    );

    // ===== Bool layer: sign-bit test, sign-fill, ASR, and NZCV flags. =====
    // These reduce through `Bool.ble`/`Bool.beq`/`Bool.and`/`Bool.not` and the
    // `if (Bool) ...` conditional (`Bool.rec`) — the increment-2 IOTA additions.

    // topSet a := Nat.ble SignBit (a % W)         (sign bit of a 64-bit value)
    def1_bool(
        &mut env,
        "AArch64.topSet",
        nat_ble(c("AArch64.SignBit"), nat_mod(bvar(0), c("AArch64.W"))),
    );
    // signFill s := W - 2^(64 - s)
    def1(
        &mut env,
        "AArch64.signFill",
        nat_sub(c("AArch64.W"), nat_pow(lit(2), nat_sub(lit(64), bvar(0)))),
    );
    // bvAsr a b := let s := b%64; let logical := (a%W) >> s;
    //   if topSet a then (logical ||| signFill s) % W else logical
    // Written with the `let`s inlined (the kernel/micro both zeta-reduce; we
    // inline so the structural mirror is a single expression). a=bvar1, b=bvar0.
    {
        let s = || nat_mod(bvar(0), lit(64));
        let logical = || nat_shr(nat_mod(bvar(1), c("AArch64.W")), s());
        let filled = nat_mod(
            nat_lor(logical(), Expr::app(c("AArch64.signFill"), s())),
            c("AArch64.W"),
        );
        let body = cond_at(
            c("Nat"),
            Expr::app(c("AArch64.topSet"), bvar(1)),
            filled,
            logical(),
        );
        def2(&mut env, "AArch64.bvAsr", body);
    }
    // 32-bit sign-bit test / sign-fill / ASR.
    def1_bool(
        &mut env,
        "AArch64.topSetW",
        nat_ble(c("AArch64.SignBitW"), nat_mod(bvar(0), c("AArch64.Ww"))),
    );
    def1(
        &mut env,
        "AArch64.signFillW",
        nat_sub(c("AArch64.Ww"), nat_pow(lit(2), nat_sub(lit(32), bvar(0)))),
    );
    {
        let s = || nat_mod(bvar(0), lit(32));
        let logical = || nat_shr(nat_mod(bvar(1), c("AArch64.Ww")), s());
        let filled = nat_mod(
            nat_lor(logical(), Expr::app(c("AArch64.signFillW"), s())),
            c("AArch64.Ww"),
        );
        let body = cond_at(
            c("Nat"),
            Expr::app(c("AArch64.topSetW"), bvar(1)),
            filled,
            logical(),
        );
        def2(&mut env, "AArch64.bvAsrW", body);
    }

    // ---- NZCV flags (64-bit) ----
    let a = || bvar(1);
    let b = || bvar(0);
    // addsN a b := topSet (bvAdd a b)
    def2_bool(
        &mut env,
        "AArch64.addsN",
        Expr::app(
            c("AArch64.topSet"),
            Expr::apps(c("AArch64.bvAdd"), [a(), b()]),
        ),
    );
    // addsZ a b := Nat.beq (bvAdd a b) 0
    def2_bool(
        &mut env,
        "AArch64.addsZ",
        nat_beq(Expr::apps(c("AArch64.bvAdd"), [a(), b()]), lit(0)),
    );
    // addsC a b := Nat.ble W ((a%W) + (b%W))
    def2_bool(
        &mut env,
        "AArch64.addsC",
        nat_ble(
            c("AArch64.W"),
            nat_add(nat_mod(a(), c("AArch64.W")), nat_mod(b(), c("AArch64.W"))),
        ),
    );
    // addsV a b := (topSet a == topSet b) && (topSet a == topSet (bvAdd a b)).not
    def2_bool(&mut env, "AArch64.addsV", {
        let r = Expr::apps(c("AArch64.bvAdd"), [a(), b()]);
        bool_and(
            bool_beq(
                Expr::app(c("AArch64.topSet"), a()),
                Expr::app(c("AArch64.topSet"), b()),
            ),
            bool_not(bool_beq(
                Expr::app(c("AArch64.topSet"), a()),
                Expr::app(c("AArch64.topSet"), r),
            )),
        )
    });
    // subsN a b := topSet (bvSub a b)
    def2_bool(
        &mut env,
        "AArch64.subsN",
        Expr::app(
            c("AArch64.topSet"),
            Expr::apps(c("AArch64.bvSub"), [a(), b()]),
        ),
    );
    // subsZ a b := Nat.beq (bvSub a b) 0
    def2_bool(
        &mut env,
        "AArch64.subsZ",
        nat_beq(Expr::apps(c("AArch64.bvSub"), [a(), b()]), lit(0)),
    );
    // subsC a b := Nat.ble W ((a%W) + (W - (b%W)))
    def2_bool(
        &mut env,
        "AArch64.subsC",
        nat_ble(
            c("AArch64.W"),
            nat_add(
                nat_mod(a(), c("AArch64.W")),
                nat_sub(c("AArch64.W"), nat_mod(b(), c("AArch64.W"))),
            ),
        ),
    );
    // subsV a b := (topSet a == topSet b).not && (topSet a == topSet (bvSub a b)).not
    def2_bool(&mut env, "AArch64.subsV", {
        let r = Expr::apps(c("AArch64.bvSub"), [a(), b()]);
        bool_and(
            bool_not(bool_beq(
                Expr::app(c("AArch64.topSet"), a()),
                Expr::app(c("AArch64.topSet"), b()),
            )),
            bool_not(bool_beq(
                Expr::app(c("AArch64.topSet"), a()),
                Expr::app(c("AArch64.topSet"), r),
            )),
        )
    });
    // CMP == SUBS flags.
    def2_bool(
        &mut env,
        "AArch64.cmpC",
        Expr::apps(c("AArch64.subsC"), [a(), b()]),
    );
    def2_bool(
        &mut env,
        "AArch64.cmpZ",
        Expr::apps(c("AArch64.subsZ"), [a(), b()]),
    );

    // ---- NZCV flags (32-bit W) ----
    def2_bool(
        &mut env,
        "AArch64.addsZW",
        nat_beq(Expr::apps(c("AArch64.bvAddW"), [a(), b()]), lit(0)),
    );
    def2_bool(
        &mut env,
        "AArch64.addsCW",
        nat_ble(
            c("AArch64.Ww"),
            nat_add(nat_mod(a(), c("AArch64.Ww")), nat_mod(b(), c("AArch64.Ww"))),
        ),
    );
    def2_bool(
        &mut env,
        "AArch64.addsNW",
        Expr::app(
            c("AArch64.topSetW"),
            Expr::apps(c("AArch64.bvAddW"), [a(), b()]),
        ),
    );
    def2_bool(&mut env, "AArch64.addsVW", {
        let r = Expr::apps(c("AArch64.bvAddW"), [a(), b()]);
        bool_and(
            bool_beq(
                Expr::app(c("AArch64.topSetW"), a()),
                Expr::app(c("AArch64.topSetW"), b()),
            ),
            bool_not(bool_beq(
                Expr::app(c("AArch64.topSetW"), a()),
                Expr::app(c("AArch64.topSetW"), r),
            )),
        )
    });
    def2_bool(
        &mut env,
        "AArch64.subsNW",
        Expr::app(
            c("AArch64.topSetW"),
            Expr::apps(c("AArch64.bvSubW"), [a(), b()]),
        ),
    );
    def2_bool(
        &mut env,
        "AArch64.subsZW",
        nat_beq(Expr::apps(c("AArch64.bvSubW"), [a(), b()]), lit(0)),
    );
    def2_bool(
        &mut env,
        "AArch64.subsCW",
        nat_ble(
            c("AArch64.Ww"),
            nat_add(
                nat_mod(a(), c("AArch64.Ww")),
                nat_sub(c("AArch64.Ww"), nat_mod(b(), c("AArch64.Ww"))),
            ),
        ),
    );

    // ---- ANDS / TST logical flags (C=0, V=0 always; N=sign, Z=zero). ----
    def2_bool(
        &mut env,
        "AArch64.andsN",
        Expr::app(
            c("AArch64.topSet"),
            Expr::apps(c("AArch64.bvAnd"), [a(), b()]),
        ),
    );
    def2_bool(
        &mut env,
        "AArch64.andsZ",
        nat_beq(Expr::apps(c("AArch64.bvAnd"), [a(), b()]), lit(0)),
    );
    def2_bool(&mut env, "AArch64.andsC", bool_false());
    def2_bool(&mut env, "AArch64.andsV", bool_false());
    def2_bool(
        &mut env,
        "AArch64.tstZ",
        Expr::apps(c("AArch64.andsZ"), [a(), b()]),
    );
    def2_bool(
        &mut env,
        "AArch64.andsNW",
        Expr::app(
            c("AArch64.topSetW"),
            Expr::apps(c("AArch64.bvAndW"), [a(), b()]),
        ),
    );
    def2_bool(
        &mut env,
        "AArch64.andsZW",
        nat_beq(Expr::apps(c("AArch64.bvAndW"), [a(), b()]), lit(0)),
    );
    def2_bool(&mut env, "AArch64.andsCW", bool_false());

    let _ = nat;
    env
}

/// One `:= rfl` theorem: `<op_app> = <rhs>` (at element type `elem_ty`, either
/// `Nat` or `Bool`) proved by `@Eq.refl <elem_ty> <op_app>`.
struct RflThm {
    name: &'static str,
    /// Element type of the stated `Eq` — `Nat` or `Bool`.
    elem_ty: Expr,
    op_app: Expr,
    rhs: Expr,
}

/// A `Nat`-valued `:= rfl` theorem.
fn thm(name: &'static str, op_app: Expr, rhs: u128) -> RflThm {
    RflThm {
        name,
        elem_ty: c("Nat"),
        op_app,
        rhs: big_lit(rhs),
    }
}

/// A `Bool`-valued `:= rfl` theorem (the NZCV/flag/topSet layer).
fn thm_bool(name: &'static str, op_app: Expr, rhs: bool) -> RflThm {
    RflThm {
        name,
        elem_ty: c("Bool"),
        op_app,
        rhs: if rhs { bool_true() } else { bool_false() },
    }
}

/// Literal for a u128 (the corpus rhs values fit in 64/128 bits).
fn big_lit(n: u128) -> Expr {
    if let Ok(small) = u64::try_from(n) {
        Expr::nat_lit(small)
    } else {
        // 2^64 .. : build via Nat.pow/Nat.add closed form so the kernel has a
        // closed Nat. We only need 2^64 here at most; encode as a BigNat lit.
        use clean_kernel::expr::{BigNat, Literal};
        let lo = (n & u128::from(u64::MAX)) as u64;
        let hi = (n >> 64) as u64;
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::from_limbs(vec![
            lo, hi,
        ]))))
    }
}

/// The targeted boundary corpus. Mirrors the curated `:= rfl` sanity theorems
/// in `proofs/aarch64_isa.lean` (the def-reducing subset).
fn targeted_corpus() -> Vec<RflThm> {
    let op = |n: &str, x: u64, y: u64| Expr::apps(c(n), [lit(x), lit(y)]);
    let op1 = |n: &str, x: u64| Expr::app(c(n), lit(x));
    vec![
        // ADD
        thm("add_wrap", op("AArch64.bvAdd", 18446744073709551615, 1), 0),
        thm("add_ok", op("AArch64.bvAdd", 100, 200), 300),
        // SUB
        thm("sub_wrap", op("AArch64.bvSub", 0, 1), 18446744073709551615),
        thm("sub_ok", op("AArch64.bvSub", 300, 100), 200),
        // MUL
        thm("mul_wrap", op("AArch64.bvMul", 4294967296, 4294967296), 0),
        thm("mul_ok", op("AArch64.bvMul", 6, 7), 42),
        // NEG
        thm("neg_one", op1("AArch64.bvNeg", 1), 18446744073709551615),
        thm("neg_invol", op1("AArch64.bvNeg", 18446744073709551615), 1),
        // AND/OR/XOR
        thm(
            "and_ok",
            op("AArch64.bvAnd", 0xFF00FF00FF00FF00, 0x0F0F0F0F0F0F0F0F),
            0x0F000F000F000F00,
        ),
        thm(
            "or_ok",
            op("AArch64.bvOr", 0xFF00000000000000, 0x00FF000000000000),
            0xFFFF000000000000,
        ),
        thm(
            "xor_ok",
            op("AArch64.bvXor", 0xAAAAAAAAAAAAAAAA, 0x5555555555555555),
            0xFFFFFFFFFFFFFFFF,
        ),
        // NOT
        thm("not_zero", op1("AArch64.bvNot", 0), 0xFFFFFFFFFFFFFFFF),
        thm("not_allones", op1("AArch64.bvNot", 0xFFFFFFFFFFFFFFFF), 0),
        // BIC / ORN
        thm(
            "bic_ok",
            op("AArch64.bvBic", 0xFFFFFFFFFFFFFFFF, 0x0F0F0F0F0F0F0F0F),
            0xF0F0F0F0F0F0F0F0,
        ),
        thm(
            "orn_ok",
            op("AArch64.bvOrn", 0x0000000000000000, 0xFFFFFFFF00000000),
            0x00000000FFFFFFFF,
        ),
        // Shifts (the #57 mask-&63 finding)
        thm("shl_mask", op("AArch64.bvShl", 1, 64), 1),
        thm("shl_ok", op("AArch64.bvShl", 1, 4), 16),
        thm("lsr_mask", op("AArch64.bvLshr", 0xFF00, 64), 0xFF00),
        thm(
            "lsr_ok",
            op("AArch64.bvLshr", 0x8000000000000000, 4),
            0x0800000000000000,
        ),
        // 32-bit W-forms
        thm("addw_wrap", op("AArch64.bvAddW", 0xFFFFFFFF, 1), 0),
        thm("addw_ok", op("AArch64.bvAddW", 100, 200), 300),
        thm(
            "addw_zero_upper",
            op("AArch64.bvAddW", 0xFFFFFFFF00000001, 0xAAAAAAAA00000002),
            0x3,
        ),
        thm("subw_wrap", op("AArch64.bvSubW", 0, 1), 0xFFFFFFFF),
        thm("subw_ok", op("AArch64.bvSubW", 300, 100), 200),
        thm("mulw_wrap", op("AArch64.bvMulW", 0x10000, 0x10000), 0),
        thm("mulw_ok", op("AArch64.bvMulW", 6, 7), 42),
        thm("negw_one", op1("AArch64.bvNegW", 1), 0xFFFFFFFF),
        thm(
            "andw_ok",
            op("AArch64.bvAndW", 0xFFFFFFFFFF00FF00, 0x000000000F0F0F0F),
            0x0F000F00,
        ),
        thm(
            "orw_zero_upper",
            op("AArch64.bvOrW", 0xFFFFFFFF0000FF00, 0x0000000000FF0000),
            0x00FFFF00,
        ),
        thm(
            "xorw_ok",
            op("AArch64.bvXorW", 0xAAAAAAAA, 0x55555555),
            0xFFFFFFFF,
        ),
        thm("notw_zero", op1("AArch64.bvNotW", 0), 0xFFFFFFFF),
        // ===== increment-2: Bool.rec / ite / Bool.beq dependent theorems =====
        // ASR (64-bit): sign-extending shift right (uses topSet + if/cond).
        thm(
            "asr_neg",
            op("AArch64.bvAsr", 0x8000000000000000, 4),
            0xF800000000000000,
        ),
        thm(
            "asr_mask",
            op("AArch64.bvAsr", 0x8000000000000000, 64),
            0x8000000000000000,
        ),
        thm(
            "asr_pos",
            op("AArch64.bvAsr", 0x7FFFFFFFFFFFFFFF, 4),
            0x07FFFFFFFFFFFFFF,
        ),
        // ASR (32-bit W): result stays < 2^32 (upper 32 zero).
        thm("asrw_neg", op("AArch64.bvAsrW", 0x80000000, 4), 0xF8000000),
        thm(
            "asrw_mask",
            op("AArch64.bvAsrW", 0x80000000, 32),
            0x80000000,
        ),
        thm("asrw_pos", op("AArch64.bvAsrW", 0x7FFFFFFF, 4), 0x07FFFFFF),
        // topSet sign-bit test (Nat.ble -> Bool, no recursor; here for coverage).
        thm_bool(
            "topset_neg",
            op1("AArch64.topSet", 0x8000000000000000),
            true,
        ),
        thm_bool(
            "topset_pos",
            op1("AArch64.topSet", 0x7FFFFFFFFFFFFFFF),
            false,
        ),
        // signFill (Nat-valued): 2^64 - 2^(64-4) = top 4 bits set.
        thm("signfill_4", op1("AArch64.signFill", 4), 0xF000000000000000),
        thm("signfill_0", op1("AArch64.signFill", 0), 0),
        // NZCV (64-bit). VERBATIM from aarch64_isa.lean.
        thm_bool(
            "adds_m1p1_Z",
            op("AArch64.addsZ", 0xFFFFFFFFFFFFFFFF, 1),
            true,
        ),
        thm_bool(
            "adds_m1p1_C",
            op("AArch64.addsC", 0xFFFFFFFFFFFFFFFF, 1),
            true,
        ),
        thm_bool(
            "adds_m1p1_N",
            op("AArch64.addsN", 0xFFFFFFFFFFFFFFFF, 1),
            false,
        ),
        thm_bool(
            "adds_m1p1_V",
            op("AArch64.addsV", 0xFFFFFFFFFFFFFFFF, 1),
            false,
        ),
        thm_bool(
            "adds_ovf_V",
            op("AArch64.addsV", 0x7FFFFFFFFFFFFFFF, 1),
            true,
        ),
        thm_bool(
            "adds_ovf_N",
            op("AArch64.addsN", 0x7FFFFFFFFFFFFFFF, 1),
            true,
        ),
        thm_bool(
            "adds_ovf_C",
            op("AArch64.addsC", 0x7FFFFFFFFFFFFFFF, 1),
            false,
        ),
        thm_bool("adds_1p1_C", op("AArch64.addsC", 1, 1), false),
        thm_bool("adds_1p1_V", op("AArch64.addsV", 1, 1), false),
        thm_bool("subs_5m3_C", op("AArch64.subsC", 5, 3), true),
        thm_bool("subs_5m3_N", op("AArch64.subsN", 5, 3), false),
        thm_bool("subs_3m5_C", op("AArch64.subsC", 3, 5), false),
        thm_bool("subs_3m5_N", op("AArch64.subsN", 3, 5), true),
        thm_bool("subs_5m5_Z", op("AArch64.subsZ", 5, 5), true),
        thm_bool("subs_5m5_C", op("AArch64.subsC", 5, 5), true),
        thm_bool(
            "subs_ovf_V",
            op("AArch64.subsV", 0x8000000000000000, 1),
            true,
        ),
        thm_bool("cmp_5m5_Z", op("AArch64.cmpZ", 5, 5), true),
        // NZCV (32-bit W).
        thm_bool("addsw_wrap_Z", op("AArch64.addsZW", 0xFFFFFFFF, 1), true),
        thm_bool("addsw_wrap_C", op("AArch64.addsCW", 0xFFFFFFFF, 1), true),
        thm_bool("addsw_ovf_V", op("AArch64.addsVW", 0x7FFFFFFF, 1), true),
        thm_bool("addsw_ovf_N", op("AArch64.addsNW", 0x7FFFFFFF, 1), true),
        thm_bool("subsw_3m5_C", op("AArch64.subsCW", 3, 5), false),
        thm_bool("subsw_3m5_N", op("AArch64.subsNW", 3, 5), true),
        thm_bool("subsw_5m5_Z", op("AArch64.subsZW", 5, 5), true),
        thm_bool("subsw_5m5_C", op("AArch64.subsCW", 5, 5), true),
        // ANDS / TST logical flags (C=0, V=0 always; N=sign, Z=zero).
        thm_bool("ands_z", op("AArch64.andsZ", 0x0F, 0xF0), true),
        thm_bool("ands_nz", op("AArch64.andsZ", 0xFF, 0x81), false),
        thm_bool(
            "ands_n",
            op("AArch64.andsN", 0x8000000000000000, 0x8000000000000000),
            true,
        ),
        thm_bool("ands_c0", op("AArch64.andsC", 0xFF, 0xFF), false),
        thm_bool("ands_v0", op("AArch64.andsV", 0xFF, 0xFF), false),
        thm_bool("tst_z", op("AArch64.tstZ", 0x0F, 0xF0), true),
        thm_bool("andsw_z", op("AArch64.andsZW", 0x0F, 0xF0), true),
        thm_bool(
            "andsw_n",
            op("AArch64.andsNW", 0x80000000, 0x80000000),
            true,
        ),
        thm_bool("andsw_c0", op("AArch64.andsCW", 0xFF, 0xFF), false),
    ]
}

/// Register a `:= rfl` theorem in the env and return its (inferred_type, cert).
/// Mirrors `clean export-cert`'s `verify_expr` path (kernel infer-with-cert).
fn kernel_check_and_cert(
    env: &mut Environment,
    t: &RflThm,
) -> (Expr, clean_kernel::cert::ProofCert) {
    // Both `Nat` and `Bool` live in `Type 0` (`Sort 1`), so `Eq.{1}` is the
    // right head for either element type.
    let elem = t.elem_ty.clone();
    let type1 = Level::succ(Level::zero());
    let stated_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
        [elem.clone(), t.op_app.clone(), t.rhs.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        [elem.clone(), t.op_app.clone()],
    );

    // STAGE 1: kernel infer-with-cert (this is what proves the rfl: the kernel
    // accepts `proof : stated_ty` only because op_app ≡ rhs).
    let tc = clean_kernel::tc::TypeChecker::new(env);
    tc.check_type(&proof, &stated_ty)
        .unwrap_or_else(|e| panic!("kernel REJECTED `{}` (not a real rfl?): {e}", t.name));
    let (inferred, cert) = tc
        .infer_type_with_cert(&proof)
        .unwrap_or_else(|e| panic!("infer-with-cert `{}`: {e}", t.name));

    // STAGE 2: CertVerifier replay (independent re-derivation of the typing).
    let mut verifier = CertVerifier::new(env);
    let (_recon, replayed) = verifier
        .replay_and_verify(&cert)
        .unwrap_or_else(|e| panic!("replay `{}`: {e}", t.name));
    assert_eq!(inferred, replayed, "replay type mismatch for `{}`", t.name);

    (inferred, cert)
}

// ---------------------------------------------------------------------------
// THE GATE
// ---------------------------------------------------------------------------

#[test]
fn diversity_gate_targeted_rfl_corpus_passes_fail_closed() {
    let mut env = build_corpus_env();

    // Build the read-only micro-env over the transitive closure of the B-def
    // roots. The micro-checker consults this for DELTA; it never touches the
    // kernel reducer.
    let roots: Vec<Name> = [
        "AArch64.W",
        "AArch64.SignBit",
        "AArch64.AllOnes",
        "AArch64.Ww",
        "AArch64.SignBitW",
        "AArch64.AllOnesW",
        "AArch64.canon",
        "AArch64.bvAdd",
        "AArch64.bvSub",
        "AArch64.bvMul",
        "AArch64.bvNeg",
        "AArch64.bvAnd",
        "AArch64.bvOr",
        "AArch64.bvXor",
        "AArch64.bvNot",
        "AArch64.bvBic",
        "AArch64.bvOrn",
        "AArch64.bvShl",
        "AArch64.bvLshr",
        "AArch64.bvAddW",
        "AArch64.bvSubW",
        "AArch64.bvMulW",
        "AArch64.bvNegW",
        "AArch64.bvAndW",
        "AArch64.bvOrW",
        "AArch64.bvXorW",
        "AArch64.bvNotW",
        // increment-2 Bool layer.
        "AArch64.topSet",
        "AArch64.signFill",
        "AArch64.bvAsr",
        "AArch64.topSetW",
        "AArch64.signFillW",
        "AArch64.bvAsrW",
        "AArch64.addsN",
        "AArch64.addsZ",
        "AArch64.addsC",
        "AArch64.addsV",
        "AArch64.subsN",
        "AArch64.subsZ",
        "AArch64.subsC",
        "AArch64.subsV",
        "AArch64.cmpC",
        "AArch64.cmpZ",
        "AArch64.addsNW",
        "AArch64.addsZW",
        "AArch64.addsCW",
        "AArch64.addsVW",
        "AArch64.subsNW",
        "AArch64.subsZW",
        "AArch64.subsCW",
        "AArch64.andsN",
        "AArch64.andsZ",
        "AArch64.andsC",
        "AArch64.andsV",
        "AArch64.tstZ",
        "AArch64.andsNW",
        "AArch64.andsZW",
        "AArch64.andsCW",
        "Bool",
        "Bool.rec",
        "Bool.and",
        "Bool.not",
        "Bool.beq",
        "Bool.true",
        "Bool.false",
        "Eq",
        "Eq.refl",
        "Nat",
    ]
    .iter()
    .map(|s| Name::from_string(s))
    .collect();
    let micro_env = MicroEnv::from_kernel(&env, &roots);
    assert!(
        micro_env.len() >= roots.len() / 2,
        "micro-env should resolve a meaningful fraction of the closure, got {}",
        micro_env.len()
    );

    let corpus = targeted_corpus();
    let total = corpus.len();
    let mut confirmed = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for t in &corpus {
        let (inferred, cert) = kernel_check_and_cert(&mut env, t);
        // Supply the stated Eq sides so the micro reducer re-derives the rfl
        // computation (op_app ≡ rhs) independently.
        let outcome = diversity_check_rfl(&micro_env, &inferred, &cert, Some((&t.op_app, &t.rhs)));
        match outcome {
            DiversityOutcome::Confirmed => confirmed += 1,
            DiversityOutcome::Disagreement(m) => {
                failures.push(format!("{}: DISAGREEMENT {m}", t.name))
            }
            DiversityOutcome::Unsupported(m) => {
                failures.push(format!("{}: UNSUPPORTED {m}", t.name))
            }
            other => failures.push(format!("{}: unexpected {other:?}", t.name)),
        }
    }

    println!(
        "DIVERSITY GATE: micro-confirmed {confirmed}/{total} targeted := rfl theorems \
         (micro-env consts: {})",
        micro_env.len()
    );

    // FAIL CLOSED: every targeted theorem must be micro-confirmed.
    assert!(
        failures.is_empty(),
        "diversity gate FAILED CLOSED on targeted decls:\n  {}",
        failures.join("\n  ")
    );
    assert_eq!(confirmed, total, "all targeted decls must be confirmed");
}

// ---------------------------------------------------------------------------
// NON-VACUITY 1: a deliberately-WRONG rfl theorem must FAIL the gate.
// ---------------------------------------------------------------------------

#[test]
fn diversity_gate_rejects_false_rfl_via_micro_reducer() {
    let env = build_corpus_env();
    let roots: Vec<Name> = ["AArch64.W", "AArch64.bvAdd", "Eq", "Eq.refl", "Nat"]
        .iter()
        .map(|s| Name::from_string(s))
        .collect();
    let micro_env = MicroEnv::from_kernel(&env, &roots);

    // FALSE: bvAdd 100 200 = 999 (truth is 300). The kernel would never accept
    // this rfl; we feed the micro reducer the false claim directly and require
    // it to DISAGREE (so the gate's reduction half is non-vacuous).
    let nat = c("Nat");
    let type1 = Level::succ(Level::zero());
    let lhs = Expr::apps(c("AArch64.bvAdd"), [lit(100), lit(200)]);
    let rhs = lit(999);
    // Forge an inferred type / cert as if rfl typed `Eq Nat lhs lhs`; the
    // TYPING half will pass (lhs : Nat), but the REDUCTION half must catch the
    // false lhs ≡ rhs.
    let inferred = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
        [nat.clone(), lhs.clone(), lhs.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        [nat.clone(), lhs.clone()],
    );
    let tc = clean_kernel::tc::TypeChecker::new(&env);
    let (_inf, cert) = tc.infer_type_with_cert(&proof).expect("infer forged proof");

    let outcome = diversity_check_rfl(&micro_env, &inferred, &cert, Some((&lhs, &rhs)));
    assert!(
        matches!(outcome, DiversityOutcome::Disagreement(_)),
        "the gate must DISAGREE on a false rfl claim, got {outcome:?}"
    );
}

// ---------------------------------------------------------------------------
// NON-VACUITY 1b (increment-2): a deliberately-WRONG rfl that turns on the NEW
// `Bool.rec` IOTA must be caught as a Disagreement. Two cases:
//   (a) a false `bvAsr` claim — `bvAsr` reduces through `if topSet a … (cond)`,
//       so catching it PROVES the new Bool.rec branch selection is load-bearing
//       (the wrong rhs is only ruled out after the true-branch sign-fill fires);
//   (b) a false `Bool`-valued NZCV claim — `subsC 3 5` is `false`, claimed
//       `true`; the micro reducer recomputes it through topSet/Nat.ble + Bool.
// ---------------------------------------------------------------------------

#[test]
fn diversity_gate_rejects_false_boolrec_rfl() {
    let env = build_corpus_env();
    let roots: Vec<Name> = [
        "AArch64.W",
        "AArch64.SignBit",
        "AArch64.bvAsr",
        "AArch64.topSet",
        "AArch64.signFill",
        "AArch64.subsC",
        "AArch64.subsN",
        "AArch64.bvSub",
        "Bool",
        "Bool.rec",
        "Bool.and",
        "Bool.not",
        "Bool.beq",
        "Bool.true",
        "Bool.false",
        "Eq",
        "Eq.refl",
        "Nat",
    ]
    .iter()
    .map(|s| Name::from_string(s))
    .collect();
    let micro_env = MicroEnv::from_kernel(&env, &roots);

    // (a) FALSE Nat-valued `bvAsr` claim: bvAsr 0x8000000000000000 4 reduces
    // (via topSet-true -> Bool.rec true-branch -> sign-fill) to
    // 0xF800000000000000, NOT 0. The micro reducer's Bool.rec IOTA must pick the
    // sign-fill branch and DISAGREE with the forged `= 0`.
    {
        let lhs = Expr::apps(c("AArch64.bvAsr"), [big_lit(0x8000000000000000), lit(4)]);
        let rhs = lit(0); // wrong: true value is 0xF800000000000000
                          // The kernel would reject this rfl, so forge inferred=`Eq Nat lhs lhs`.
        let nat = c("Nat");
        let type1 = Level::succ(Level::zero());
        let inferred = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            [nat.clone(), lhs.clone(), lhs.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
            [nat.clone(), lhs.clone()],
        );
        let tc = clean_kernel::tc::TypeChecker::new(&env);
        let (_inf, cert) = tc
            .infer_type_with_cert(&proof)
            .expect("infer forged asr proof");
        let outcome = diversity_check_rfl(&micro_env, &inferred, &cert, Some((&lhs, &rhs)));
        assert!(
            matches!(outcome, DiversityOutcome::Disagreement(_)),
            "false bvAsr (Bool.rec branch) must DISAGREE, got {outcome:?}"
        );
    }

    // (b) FALSE Bool-valued NZCV claim: subsC 3 5 = false (3 <u 5 -> borrow),
    // claimed `true`. The micro reducer recomputes the flag and must DISAGREE.
    {
        let lhs = Expr::apps(c("AArch64.subsC"), [lit(3), lit(5)]);
        let rhs = bool_true(); // wrong: true value is Bool.false
        let bool_ty = c("Bool");
        let type1 = Level::succ(Level::zero());
        let inferred = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            [bool_ty.clone(), lhs.clone(), lhs.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
            [bool_ty.clone(), lhs.clone()],
        );
        let tc = clean_kernel::tc::TypeChecker::new(&env);
        let (_inf, cert) = tc
            .infer_type_with_cert(&proof)
            .expect("infer forged subsC proof");
        let outcome = diversity_check_rfl(&micro_env, &inferred, &cert, Some((&lhs, &rhs)));
        assert!(
            matches!(outcome, DiversityOutcome::Disagreement(_)),
            "false subsC (Bool-valued) must DISAGREE, got {outcome:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// NON-VACUITY 2: an unmodelable recursor (bvAsr uses Bool/ite) must be
// reported UNSUPPORTED — FAIL CLOSED, not silently skipped.
// ---------------------------------------------------------------------------

#[test]
fn diversity_gate_honest_defers_unmodelable_recursor_fail_closed() {
    // A `:= rfl` whose proof needs a RECURSOR the micro reducer does NOT model.
    // Increment 2 added `Bool.rec` and `Nat.rec` to the micro engine, so the
    // probe must use a recursor OUTSIDE that allowlist — `List.rec` (via the
    // prelude's `List.length`). The kernel proves `List.length [10,20] = 2` by
    // IOTA on `List.rec`; the micro-checker delta-unfolds `List.length` to its
    // `List.rec` body, hits the unmodeled recursor, gets STUCK, and must
    // surface UNSUPPORTED (fail-closed) — NOT a silent confirm, NOT a
    // misleading disagreement. This keeps the deferral teeth honest as the
    // recursor set grows.
    let env = Environment::with_prelude();
    let nat = c("Nat");
    let type1 = Level::succ(Level::zero());
    // The List combinators are universe-polymorphic over the ELEMENT universe;
    // for `List Nat` (with `Nat : Type 0`) that level param is `0`.
    let elem_u = Level::zero();

    // Closed `List Nat` = [10, 20] : @List.cons Nat 10 (@List.cons Nat 20 (@List.nil Nat)).
    let list_nil = Expr::apps(
        Expr::const_(Name::from_string("List.nil"), vec![elem_u.clone()]),
        [nat.clone()],
    );
    let cons = |hd: Expr, tl: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![elem_u.clone()]),
            [nat.clone(), hd, tl],
        )
    };
    let list_2 = cons(lit(10), cons(lit(20), list_nil));

    // lhs := @List.length Nat [10,20] ; rhs := 2 (TRUE, proved by List.rec iota).
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("List.length"), vec![elem_u.clone()]),
        [nat.clone(), list_2],
    );
    let rhs = lit(2);

    let roots: Vec<Name> = [
        "List.length",
        "List.rec",
        "List.nil",
        "List.cons",
        "List",
        "Nat",
        "Nat.succ",
        "Eq",
        "Eq.refl",
    ]
    .iter()
    .map(|s| Name::from_string(s))
    .collect();
    let micro_env = MicroEnv::from_kernel(&env, &roots);

    let stated_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
        [nat.clone(), lhs.clone(), rhs.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![type1]),
        [nat.clone(), lhs.clone()],
    );
    let tc = clean_kernel::tc::TypeChecker::new(&env);
    // The kernel DOES accept this (List.rec reduces via iota in the kernel).
    tc.check_type(&proof, &stated_ty)
        .expect("kernel proves List.length rfl");
    let (inferred, cert) = tc.infer_type_with_cert(&proof).expect("infer");

    // ...but the micro reducer does NOT model List.rec -> must FAIL CLOSED
    // (Unsupported), NOT silently confirm.
    let outcome = diversity_check_rfl(&micro_env, &inferred, &cert, Some((&lhs, &rhs)));
    assert!(
        matches!(outcome, DiversityOutcome::Unsupported(_)),
        "an unmodelable op must be UNSUPPORTED (fail-closed), got {outcome:?}"
    );
}
