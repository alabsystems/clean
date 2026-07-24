// Independent adversarial verification of the width-N gate-fidelity claim.
// NOT trusting the implementer's own tests. Forges UNSOUND wider encodings and
// confirms the kernel re-check (which reduces the actual gate trees) REJECTS them.

use clean_kernel::bitvec_compute::BvNames;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, Level, TypeChecker};

fn env_width(n: u32) -> Environment {
    let mut env = Environment::with_prelude();
    env.init_bv_compute_width(n).expect("init width");
    env
}

fn btrue() -> Expr {
    Expr::const_str("Bool.true")
}
fn bfalse() -> Expr {
    Expr::const_str("Bool.false")
}

/// `Clean.BV{n}.mk` of a concrete u64 value, LSB = bit0.
fn mk_value(nm: BvNames, value: u64) -> Expr {
    let bits: Vec<Expr> = (0..nm.width)
        .map(|k| {
            if (value >> k) & 1 == 1 {
                btrue()
            } else {
                bfalse()
            }
        })
        .collect();
    Expr::apps(Expr::const_str(&nm.bv_mk()), bits)
}

fn eq_bv(nm: BvNames, lhs: Expr, rhs: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![u1]),
        [Expr::const_str(&nm.bv()), lhs, rhs],
    )
}

/// Does `bvAdd (mk x) (mk y)` reduce to `mk claimed` under the kernel?  Returns
/// Ok if the kernel ACCEPTS the refl-proof, Err if it REJECTS.
fn add_reduces_to(n: u32, x: u64, y: u64, claimed: u64) -> Result<(), String> {
    let nm = BvNames::new(n);
    let e = env_width(n);
    let mask = if n >= 64 { u64::MAX } else { (1u64 << n) - 1 };
    let lhs = Expr::apps(
        Expr::const_str(&nm.bv_add()),
        [mk_value(nm, x & mask), mk_value(nm, y & mask)],
    );
    let rhs = mk_value(nm, claimed & mask);
    let goal = eq_bv(nm, lhs, rhs.clone());
    let u1 = Level::succ(Level::zero());
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [Expr::const_str(&nm.bv()), rhs],
    );
    let tc = TypeChecker::with_mode(&e, e.mode());
    tc.check_type(&refl, &goal)
        .map_err(|err| format!("{err:?}"))
}

#[test]
fn width8_and_16_real_sums_accepted_wrong_sums_rejected() {
    // Brute-force a spread of concrete value pairs at width 8: the kernel must
    // accept exactly the TRUE ripple-carry sum and reject EVERY off-by-one-bit
    // forgery. This is the faithful-encoding claim made adversarial.
    let n = 8u32;
    let cases: &[(u64, u64)] = &[
        (0x00, 0x00),
        (0x0F, 0x01), // carry across nibble
        (0xFF, 0x01), // full wrap
        (0x55, 0x2A),
        (0x80, 0x80), // overflow drops MSB carry
        (0x7F, 0x01), // carry ripples through all low bits
        (0xAB, 0xCD),
        (0x01, 0xFF),
    ];
    for &(x, y) in cases {
        let real = (x.wrapping_add(y)) & 0xFF;
        add_reduces_to(n, x, y, real)
            .unwrap_or_else(|e| panic!("TRUE sum {x:#x}+{y:#x}={real:#x} must be accepted: {e}"));
        // every single-bit corruption of the real sum must be REJECTED
        for bit in 0..n {
            let forged = real ^ (1u64 << bit);
            assert!(
                add_reduces_to(n, x, y, forged).is_err(),
                "FORGED width-8 sum {x:#x}+{y:#x}={forged:#x} (bit {bit} flipped from {real:#x}) \
                 must be REJECTED by the kernel gate-tree reduction"
            );
        }
    }
}

#[test]
fn width16_carry_propagation_is_real_not_xor() {
    // The single most important soundness probe: distinguish a genuine ripple
    // carry from a degenerate per-bit XOR (which would IGNORE carry-in). For
    // 0x00FF + 0x0001, plain XOR gives 0x00FE (wrong); the real carry gives 0x0100.
    let n = 16u32;
    add_reduces_to(n, 0x00FF, 0x0001, 0x0100).expect("real ripple carry => 0x0100");
    assert!(
        add_reduces_to(n, 0x00FF, 0x0001, 0x00FE).is_err(),
        "a carry-ignoring XOR sum (0x00FE) MUST be rejected — proves carry is real"
    );
    // and a long carry chain: 0x7FFF + 1 = 0x8000 (carry through 15 bits).
    add_reduces_to(n, 0x7FFF, 0x0001, 0x8000).expect("15-bit carry chain => 0x8000");
    assert!(
        add_reduces_to(n, 0x7FFF, 0x0001, 0x0000).is_err(),
        "dropped long carry chain must be rejected"
    );
}

#[test]
fn forged_unsound_bit_blast_definition_is_rejected_by_kernel() {
    // FORGE an UNSOUND wider encoding directly: register a width-8 alternative
    // "adder" `bvAddBad` whose output bit i is the XOR of x_i,y_i ONLY (no carry),
    // then ASSERT that bvAddBad does NOT agree with the real bvAdd on a value
    // where carry matters. i.e. the kernel can SEE the two gate trees differ —
    // it never silently treats the bad encoding as the real bvAdd.
    let n = 8u32;
    let nm = BvNames::new(n);
    let mut e = env_width(n);

    // bvAddBad x y := mk (xor (bit0 x)(bit0 y)) .. (xor (bit7 x)(bit7 y))
    let bv = Expr::const_str(&nm.bv());
    let bit = |v: &Expr, k: u32| Expr::app(Expr::const_str(&nm.bit(k)), v.clone());
    let bxor = |a: Expr, b: Expr| Expr::apps(Expr::const_str("Bool.xor"), [a, b]);
    let value = {
        // fun (x y : BV8) => mk (xor (bit_k x)(bit_k y))_k   -- de Bruijn: y=#0, x=#1
        let x = Expr::bvar(1);
        let y = Expr::bvar(0);
        let bits: Vec<Expr> = (0..n).map(|k| bxor(bit(&x, k), bit(&y, k))).collect();
        let body = Expr::apps(Expr::const_str(&nm.bv_mk()), bits);
        let inner = Expr::lam(clean_kernel::BinderInfo::Default, bv.clone(), body);
        Expr::lam(clean_kernel::BinderInfo::Default, bv.clone(), inner)
    };
    let ty = Expr::arrow(bv.clone(), Expr::arrow(bv.clone(), bv.clone()));
    e.add_decl(clean_kernel::Declaration::Definition {
        name: Name::from_string("Clean.BV8.bvAddBad"),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("the bad def itself type-checks (it is a well-typed but WRONG adder)");

    // On 0x0F + 0x01: real bvAdd = 0x10, bvAddBad (carry-free xor) = 0x0E.
    // The kernel re-check of "bvAddBad x y == real bvAdd x y" MUST FAIL, proving
    // the kernel reduces the actual distinct gate trees and would never accept a
    // bit-blast whose bit i != the real bvAdd bit i.
    let x = mk_value(nm, 0x0F);
    let y = mk_value(nm, 0x01);
    let bad = Expr::apps(
        Expr::const_str("Clean.BV8.bvAddBad"),
        [x.clone(), y.clone()],
    );
    let real = Expr::apps(Expr::const_str(&nm.bv_add()), [x, y]);
    let goal = eq_bv(nm, bad.clone(), real);
    let u1 = Level::succ(Level::zero());
    // try to "prove" bad == real by refl of bad (would only work if defeq)
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [Expr::const_str(&nm.bv()), bad],
    );
    let tc = TypeChecker::with_mode(&e, e.mode());
    assert!(
        tc.check_type(&refl, &goal).is_err(),
        "kernel MUST reject equating a carry-free forged adder with the real bvAdd"
    );

    // And positively: bvAddBad actually reduces to the WRONG value 0x0E, proving
    // the kernel really evaluates gate trees (so a faithful encoding's acceptance
    // is meaningful, not vacuous).
    let x2 = mk_value(nm, 0x0F);
    let y2 = mk_value(nm, 0x01);
    let bad2 = Expr::apps(Expr::const_str("Clean.BV8.bvAddBad"), [x2, y2]);
    let wrong = mk_value(nm, 0x0E);
    let goal2 = eq_bv(nm, bad2, wrong.clone());
    let u1b = Level::succ(Level::zero());
    let refl2 = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1b]),
        [Expr::const_str(&nm.bv()), wrong],
    );
    let tc2 = TypeChecker::with_mode(&e, e.mode());
    tc2.check_type(&refl2, &goal2)
        .expect("forged carry-free adder reduces to the WRONG 0x0E (kernel evaluates trees)");
}

#[test]
fn forged_bv8_carrier_wrong_arity_is_rejected() {
    // A wrong-WIDTH encoding: try to use a 7-bit mk where an 8-bit one is needed.
    // The kernel must reject the under-applied constructor (width is real, not a
    // free parameter the bit-blast can fudge).
    let n = 8u32;
    let nm = BvNames::new(n);
    let e = env_width(n);
    // mk with only 7 bits — under-applied; using it as a BV8 must fail.
    let seven: Vec<Expr> = (0..7).map(|_| bfalse()).collect();
    let bad_mk = Expr::apps(Expr::const_str(&nm.bv_mk()), seven);
    let goal = eq_bv(nm, bad_mk.clone(), mk_value(nm, 0));
    let u1 = Level::succ(Level::zero());
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![u1]),
        [Expr::const_str(&nm.bv()), bad_mk],
    );
    let tc = TypeChecker::with_mode(&e, e.mode());
    assert!(
        tc.check_type(&refl, &goal).is_err(),
        "under-applied 7-bit mk must not pass as a BV8 (width is structural)"
    );
}
