// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.3 review: adversarial vectors the implementation's own tests did not
//! write. A child of `emit_trust_ir::tests::ws6_3`, so the
//! `trust-ir-backend-lib` gate leg (`-- emit_trust_ir`) runs it.
//!
//! The implementation's differential covers `mask` at `UInt64` only and
//! reaches `Nat.xor` only through the bare runtime entry point. This file
//! drives, through BOTH native lanes and against kernel-certified values:
//!
//! * the NARROW widths' native `and`/`or` (`UInt8/16/32`), with the top bit
//!   of the width set, so a sign-extending or width-confused lowering shows;
//! * `UInt64.land`/`lor` as a FUNCTION VALUE (the boxed-entry wrapper the
//!   0-arg `Apply` materializes), fed operands ≥ 2^63, which the wrapper must
//!   unbox from a HEAP cell (the WS6.1 class);
//! * the RC contract of the arg-consuming shims: one heap `Nat` passed to
//!   `Nat.land`/`lor`/`xor` several times (`a &&& a`, `a ^^^ a`) — a shim
//!   that consumed what the caller's RC discipline treats as borrowed (or the
//!   reverse) frees a live cell and corrupts or aborts the later reads;
//! * `Nat.xor` through the compiled pipeline, including heap operands whose
//!   result is small enough to be a TAGGED immediate.

use super::*;

/// The widths of the native `and`/`or` vectors: `(kernel type, bits)`.
const REVIEW_WIDTHS: [(&str, u32); 4] =
    [("UInt8", 8), ("UInt16", 16), ("UInt32", 32), ("UInt64", 64)];

/// `UIntW.ofNat n` as a kernel term.
fn uint_lit(w: &str, n: u128) -> clean_kernel::Expr {
    clean_kernel::Expr::app(
        clean_kernel::Expr::const_str(&format!("{w}.ofNat")),
        clean_kernel::Expr::nat_lit_u128(n),
    )
}

/// The C scalar type of a width.
fn c_ty(bits: u32) -> &'static str {
    match bits {
        8 => "uint8_t",
        16 => "uint16_t",
        32 => "uint32_t",
        _ => "uint64_t",
    }
}

/// One driver call: `(root, operands, expected)`. Operands and results are
/// `u128` so the `Nat` roots can use two-limb heap values.
struct Call {
    root: String,
    args: Vec<u128>,
    want: u128,
}

/// The review environment and its driver calls. Every expected value is
/// certified by the kernel (`rfl`), and every expected value off by one is
/// REFUSED by it, so the differential compares against the kernel, not
/// against a Rust re-statement.
fn review_env() -> (clean_kernel::Environment, Vec<String>, Vec<Call>) {
    use clean_kernel::env::Declaration;
    use clean_kernel::{BinderInfo, Environment, Expr as KExpr};
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    let mut roots = Vec::new();
    let mut calls = Vec::new();
    let add = |env: &mut Environment, name: &str, ty: KExpr, value: KExpr| {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
        .unwrap_or_else(|e| panic!("`{name}` kernel-checks against the prelude: {e:?}"));
    };
    let bin = |t: &KExpr, body: KExpr| {
        KExpr::lam(
            BinderInfo::Default,
            t.clone(),
            KExpr::lam(BinderInfo::Default, t.clone(), body),
        )
    };
    let arrow2 = |t: &KExpr| KExpr::arrow(t.clone(), KExpr::arrow(t.clone(), t.clone()));

    // (1) Narrow and full widths, native and/or, top bit set.
    for (w, bits) in REVIEW_WIDTHS {
        let t = KExpr::const_str(w);
        let max: u128 = (1u128 << bits) - 1;
        let top: u128 = 1u128 << (bits - 1);
        for (op, spec) in [
            ("land", (|a, b| a & b) as fn(u128, u128) -> u128),
            ("lor", |a, b| a | b),
        ] {
            let root = format!("ws6_3_rv_{op}_{w}");
            add(
                &mut env,
                &root,
                arrow2(&t),
                bin(
                    &t,
                    KExpr::apps(
                        KExpr::const_str(&format!("{w}.{op}")),
                        [KExpr::bvar(1), KExpr::bvar(0)],
                    ),
                ),
            );
            for (a, b) in [(max, top + 1), (top | 5, 3), (top | 0x5a, top | 0x33)] {
                calls.push(Call {
                    root: root.clone(),
                    args: vec![a, b],
                    want: spec(a, b),
                });
            }
            roots.push(root);
        }
    }

    // (2) `UInt64.land`/`lor` as a FUNCTION VALUE through a higher-order
    // apply: the 0-arg `Apply` path and its synthesized boxed-entry wrapper.
    let u64t = KExpr::const_str("UInt64");
    let fn_t = arrow2(&u64t);
    add(
        &mut env,
        "ws6_3_rv_apply2",
        KExpr::arrow(fn_t.clone(), arrow2(&u64t)),
        KExpr::lam(
            BinderInfo::Default,
            fn_t,
            bin(
                &u64t,
                KExpr::apps(KExpr::bvar(2), [KExpr::bvar(1), KExpr::bvar(0)]),
            ),
        ),
    );
    for (op, spec) in [
        ("land", (|a, b| a & b) as fn(u128, u128) -> u128),
        ("lor", |a, b| a | b),
    ] {
        let root = format!("ws6_3_rv_hof_{op}");
        add(
            &mut env,
            &root,
            arrow2(&u64t),
            bin(
                &u64t,
                KExpr::apps(
                    KExpr::const_str("ws6_3_rv_apply2"),
                    [
                        KExpr::const_str(&format!("UInt64.{op}")),
                        KExpr::bvar(1),
                        KExpr::bvar(0),
                    ],
                ),
            ),
        );
        for (a, b) in [
            ((1u128 << 63) + 5, (1u128 << 63) + 3),
            (u128::from(u64::MAX), 1u128 << 63),
            (12, 10),
        ] {
            calls.push(Call {
                root: root.clone(),
                args: vec![a, b],
                want: spec(a, b),
            });
        }
        roots.push(root);
    }

    // (3) RC contract: one `Nat` read four times across the three shims,
    // `(a &&& a) + (a ||| (a ^^^ a)) = 2a`.
    let nat = KExpr::const_str("Nat");
    let app2 = |f: &str, x: KExpr, y: KExpr| KExpr::apps(KExpr::const_str(f), [x, y]);
    add(
        &mut env,
        "ws6_3_rv_nat_reuse",
        KExpr::arrow(nat.clone(), nat.clone()),
        KExpr::lam(
            BinderInfo::Default,
            nat.clone(),
            app2(
                "Nat.add",
                app2("Nat.land", KExpr::bvar(0), KExpr::bvar(0)),
                app2(
                    "Nat.lor",
                    KExpr::bvar(0),
                    app2("Nat.xor", KExpr::bvar(0), KExpr::bvar(0)),
                ),
            ),
        ),
    );
    for a in [5u128, (1 << 64) + 3, (1 << 126) + 1, (1 << 63) + 9] {
        calls.push(Call {
            root: "ws6_3_rv_nat_reuse".into(),
            args: vec![a],
            want: 2 * a,
        });
    }
    roots.push("ws6_3_rv_nat_reuse".into());

    // (4) `Nat.xor` compiled, heap operands with a TAGGED result, and wide
    // results.
    add(
        &mut env,
        "ws6_3_rv_nat_xor",
        arrow2(&nat),
        bin(&nat, app2("Nat.xor", KExpr::bvar(1), KExpr::bvar(0))),
    );
    for (a, b) in [
        ((1u128 << 64) + 5, (1u128 << 64) + 3),
        ((1u128 << 127) + 1, 1),
        (1u128 << 63, 1u128 << 63),
        (u128::MAX, 1u128 << 100),
    ] {
        calls.push(Call {
            root: "ws6_3_rv_nat_xor".into(),
            args: vec![a, b],
            want: a ^ b,
        });
    }
    roots.push("ws6_3_rv_nat_xor".into());

    // Kernel certification of every call, and refusal of each off by one.
    for (i, c) in calls.iter().enumerate() {
        let (ty, lit): (KExpr, Box<dyn Fn(u128) -> KExpr>) = match review_sig(&c.root) {
            RvSig::Uint(w, _) => (KExpr::const_str(w), Box::new(move |n| uint_lit(w, n))),
            RvSig::Nat1 | RvSig::Nat2 => (nat.clone(), Box::new(KExpr::nat_lit_u128)),
        };
        let lhs = KExpr::apps(
            KExpr::const_str(&c.root),
            c.args.iter().map(|&a| lit(a)).collect::<Vec<_>>(),
        );
        env.add_decl(ws6_3_rfl(
            &format!("ws6_3_rv_vector_{i}"),
            ty.clone(),
            lhs.clone(),
            lit(c.want),
        ))
        .unwrap_or_else(|e| {
            panic!(
                "the kernel must certify `{} {:?} = {}`: {e:?}",
                c.root, c.args, c.want
            )
        });
        let wrong = match review_sig(&c.root) {
            RvSig::Uint(_, bits) => (c.want + 1) & ((1u128 << bits) - 1),
            _ => c.want.wrapping_add(1),
        };
        assert!(
            env.add_decl(ws6_3_rfl(
                &format!("ws6_3_rv_off_by_one_{i}"),
                ty,
                lhs,
                lit(wrong)
            ))
            .is_err(),
            "the kernel must REFUSE `{} {:?} = {wrong}`",
            c.root,
            c.args
        );
    }
    (env, roots, calls)
}

/// The C shape of a review root.
enum RvSig {
    /// `(uintW, uintW) -> uintW`: the kernel type name and its bit width.
    Uint(&'static str, u32),
    /// `(clean_obj*) -> clean_obj*`.
    Nat1,
    /// `(clean_obj*, clean_obj*) -> clean_obj*`.
    Nat2,
}

fn review_sig(root: &str) -> RvSig {
    if root == "ws6_3_rv_nat_reuse" {
        return RvSig::Nat1;
    }
    if root == "ws6_3_rv_nat_xor" {
        return RvSig::Nat2;
    }
    if root.starts_with("ws6_3_rv_hof_") {
        return RvSig::Uint("UInt64", 64);
    }
    REVIEW_WIDTHS
        .iter()
        .find(|(w, _)| root.ends_with(&format!("_{w}")))
        .map(|&(w, bits)| RvSig::Uint(w, bits))
        .unwrap_or_else(|| panic!("no signature for `{root}`"))
}

/// The driver: one prototype per root (`symbol` spells its link name), then a
/// `main` that makes every call and prints one decimal result per line.
fn review_driver(
    roots: &[String],
    calls: &[Call],
    symbol: impl Fn(&str, &str) -> String,
) -> String {
    let mut s = String::from(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n\
         static void ws_put(unsigned __int128 v) {\n\
           char buf[64]; int i = 63; buf[i] = 0;\n\
           if (v == 0) { buf[--i] = '0'; }\n\
           while (v > 0) { buf[--i] = (char)('0' + (unsigned)(v % 10)); v /= 10; }\n\
           printf(\"%s\\n\", buf + i);\n\
         }\n\
         static void ws_rc(clean_obj* o) {\n\
           if (clean_is_scalar(o)) { printf(\"rc -\\n\"); return; }\n\
           printf(\"rc %u\\n\", (unsigned)atomic_load(&o->header.ref_count));\n\
         }\n",
    );
    for (i, root) in roots.iter().enumerate() {
        let proto = match review_sig(root) {
            RvSig::Uint(_, bits) => {
                let t = c_ty(bits);
                format!("{t} rv_{i}({t}, {t})")
            }
            RvSig::Nat1 => format!("clean_obj* rv_{i}(clean_obj*)"),
            RvSig::Nat2 => format!("clean_obj* rv_{i}(clean_obj*, clean_obj*)"),
        };
        s.push_str(&format!("{};\n", symbol(&proto, root)));
    }
    s.push_str("int main(void) {\n");
    let nat = |v: u128| format!("clean_nat_big({}ull, {}ull)", v as u64, (v >> 64) as u64);
    for c in calls {
        let i = roots.iter().position(|r| *r == c.root).expect("root");
        let line = match review_sig(&c.root) {
            RvSig::Uint(_, bits) => format!(
                "ws_put((unsigned __int128)rv_{i}(({t}){}ull, ({t}){}ull));",
                c.args[0] as u64,
                c.args[1] as u64,
                t = c_ty(bits)
            ),
            // The driver keeps its OWN reference to every heap operand
            // across the call, then reads the cell's refcount: the root must
            // hand back exactly what it was given (`rc 0` = one reference,
            // the driver's). An over-consuming shim frees a live cell (the
            // count wraps or the value is garbage); a leaking one leaves
            // `rc` above 0.
            RvSig::Nat1 => format!(
                "{{ clean_obj* a = {}; clean_inc(a); clean_obj* r = rv_{i}(a); \
                 ws_put(clean_nat_to_u128(r)); clean_dec(r); ws_rc(a); clean_dec(a); }}",
                nat(c.args[0])
            ),
            RvSig::Nat2 => format!(
                "{{ clean_obj* a = {}; clean_obj* b = {}; clean_inc(a); clean_inc(b); \
                 clean_obj* r = rv_{i}(a, b); ws_put(clean_nat_to_u128(r)); \
                 printf(\"tag %d\\n\", clean_is_scalar(r) ? 1 : 0); clean_dec(r); \
                 ws_rc(a); ws_rc(b); clean_dec(a); clean_dec(b); }}",
                nat(c.args[0]),
                nat(c.args[1])
            ),
        };
        s.push_str(&line);
        s.push('\n');
    }
    s.push_str("return 0;\n}\n");
    s
}

/// The expected driver output: one value per call, then for a `Nat` root the
/// result's representation (tagged iff below 2^63, `Nat.xor` only) and each
/// operand's refcount after the call (`rc -` for a tagged operand, `rc 0` —
/// exactly the driver's own reference — for a heap one).
fn review_want(calls: &[Call]) -> Vec<String> {
    let rc = |v: u128| {
        if v < (1 << 63) {
            "rc -".to_string()
        } else {
            "rc 0".to_string()
        }
    };
    let mut want = Vec::new();
    for c in calls {
        want.push(c.want.to_string());
        match review_sig(&c.root) {
            RvSig::Nat1 => want.push(rc(c.args[0])),
            RvSig::Nat2 => {
                want.push(format!("tag {}", u8::from(c.want < (1 << 63))));
                want.push(rc(c.args[0]));
                want.push(rc(c.args[1]));
            }
            RvSig::Uint(..) => {}
        }
    }
    want
}

fn review_compare(lane: &str, got: &str, calls: &[Call]) {
    let want = review_want(calls);
    let got: Vec<&str> = got.lines().collect();
    assert_eq!(
        got.len(),
        want.len(),
        "{lane}: one line per result: {got:?}"
    );
    for (i, (g, w)) in got.iter().zip(&want).enumerate() {
        assert_eq!(g, w, "{lane}: line {i} (want {w}); full output {got:?}");
    }
}

/// Adversarial vectors, both lanes, against kernel-certified values.
#[test]
fn test_ws6_3_review_narrow_widths_function_values_and_shim_rc() {
    // SELF-SKIP OK: the native lanes need an aarch64/x86_64 host (ws6_1_host); on any other arch nothing can be built or run, and the skip is printed.
    let Some(host) = ws6_1_host() else {
        eprintln!("WS6.3 review skipped: unsupported host arch");
        return;
    };
    let (env, roots, calls) = review_env();
    let root_refs: Vec<&str> = roots.iter().map(String::as_str).collect();
    let decls = ws6_1_closure_shimming(&env, &root_refs, WS6_3_NAT_SHIMMED);
    let art = crate::pass_manager::compile_lcnf_decls(
        &decls,
        &env,
        &crate::pass_manager::PipelineConfig::default(),
    )
    .expect("the review closure compiles through the real pipeline");
    let dir = tempfile::tempdir().expect("tempdir");
    let shims = ws6_3_nat_shims_c();

    // --emit c: one TU; each alias is a macro onto the mangled name.
    let c_code = art
        .emit_c(crate::emit_c::CEmitConfig::default())
        .expect("the review closure lowers to C");
    let m = |s: &str| crate::mangle::mangle_name(&Name::from_string(s));
    let mut tu = format!(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n{shims}\n{c_code}\n"
    );
    for (i, root) in roots.iter().enumerate() {
        tu.push_str(&format!("#define rv_{i} {}\n", m(root)));
    }
    // The prototypes would redeclare the (static) emitted functions under
    // the macro: spell them as comments in this lane.
    tu.push_str(&review_driver(&roots, &calls, |proto, _| {
        format!("/* {proto} */")
    }));
    let got = ws6_1_build_and_run(dir.path(), "review_c", &[("tu.c", tu.clone())], &[], host.1);
    review_compare("emit_c", &got, &calls);

    // MUTATION CONTROL for the refcount lines: a `l_Nat_land` shim that
    // retains its first operand (a one-reference leak, values unchanged)
    // must be caught on a heap operand's `rc 0` line — so those lines
    // observe the shims' RC contract rather than restating it.
    let real = "{ return clean_nat_land(a, b); }";
    assert!(
        tu.contains(real),
        "the shim text moved; update the mutation"
    );
    let leaky = tu.replacen(real, "{ clean_inc(a); return clean_nat_land(a, b); }", 1);
    let got = ws6_1_build_and_run(dir.path(), "review_c_leak", &[("tu.c", leaky)], &[], host.1);
    let want = review_want(&calls);
    let got: Vec<&str> = got.lines().collect();
    assert_eq!(got.len(), want.len(), "leaky shim: {got:?}");
    assert!(
        got.iter()
            .zip(&want)
            .any(|(g, w)| w == "rc 0" && *g != "rc 0"),
        "a leaking `l_Nat_land` must show on a heap operand's refcount: {got:?}"
    );
    assert!(
        got.iter()
            .zip(&want)
            .all(|(g, w)| w.starts_with("rc ") || g == w),
        "the leak must move ONLY refcount lines: {got:?}"
    );

    let module = art
        .emit_trust_ir(&ws6_1_extern_config())
        .expect("the review closure lowers to trust-ir");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
    // The function-value roots must really build a closure, and the closure's
    // code pointer is the primitive's boxed entry, which must itself be the
    // native op (unbox, `and`/`or` at u64, box) — or (2) is vacuous.
    let func = |name: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("`{name}` is not emitted"))
    };
    let alloc_closure = ws6_1_runtime_fn(&module, "clean_alloc_closure");
    for (op, native) in [("land", BinOp::And), ("lor", BinOp::Or)] {
        let root = func(&format!("ws6_3_rv_hof_{op}"));
        let builds_closure = root.instructions().any(|n| {
            matches!(&n.inst, trust_ir::inst::Inst::Call { callee, .. }
                if *callee == alloc_closure)
        });
        assert!(
            builds_closure,
            "`{}` must pass `UInt64.{op}` as a closure",
            root.name
        );
        let boxed = func(&format!("l_UInt64_{op}___boxed"));
        let (ops, _) = ws6_3_ops_and_calls(boxed);
        assert_eq!(
            ops,
            vec![(native, Ty::U64)],
            "`{}` (the closure's code) must be the native {native:?}",
            boxed.name
        );
    }
    // SELF-SKIP OK: only the trust-cg compile/link/run leg needs the external trust-cg binary (find_trust_cg: CLEAN_TRUST_CG_BIN / ../trust-cg / PATH); emit_trust_ir, validate_module and the closure/native-op asserts above run on every box, and the skip is printed.
    let Some(trust_cg) = find_trust_cg() else {
        eprintln!("WS6.3 review trust-ir native leg skipped: trust-cg binary not found");
        return;
    };
    let p = if cfg!(target_os = "macos") { "_" } else { "" };
    let driver = review_driver(&roots, &calls, |proto, root| {
        format!("extern {proto} __asm__(\"{p}{root}\")")
    });
    let tmbc = dir.path().join("review_ti.tmbc");
    let obj = dir.path().join("review_ti.o");
    write_legacy_native_fixture(&module, &trust_cg, host.0, &tmbc);
    let cg = legacy_trust_cg(&trust_cg)
        .args(["-c", "--target", host.0, "-o"])
        .arg(&obj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "trust-cg failed: {}",
        String::from_utf8_lossy(&cg.stderr)
    );
    let rt_extern = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../clean-runtime/src/runtime_extern.c");
    let rt_extern = std::fs::read_to_string(rt_extern).expect("read runtime_extern.c");
    let got = ws6_1_build_and_run(
        dir.path(),
        "review_ti",
        &[
            ("driver.c", driver),
            ("shims.c", format!("#include \"clean_runtime.h\"\n{shims}")),
            ("runtime_extern.c", rt_extern),
        ],
        &[&obj],
        host.1,
    );
    review_compare("trust-ir", &got, &calls);
}
