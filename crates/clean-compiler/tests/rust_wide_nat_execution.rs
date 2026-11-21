// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compile actual emitted Rust against the real runtime, then execute it.
#![cfg(feature = "round-trip-compile")]

use clean_compiler::ir::{IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn capture(mut command: Command, root: &Path, name: &str) -> Output {
    let argv = std::iter::once(command.get_program())
        .chain(command.get_args())
        .map(|s| s.to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    let output = command.output().expect("run the real tool/control");
    std::fs::write(root.join(format!("{name}.stdout")), &output.stdout).unwrap();
    std::fs::write(root.join(format!("{name}.stderr")), &output.stderr).unwrap();
    std::fs::write(
        root.join(format!("{name}.json")),
        serde_json::to_vec_pretty(&serde_json::json!({
            "argv": argv,
            "cwd": std::env::current_dir().unwrap(),
            "exit": output.status.code(),
        }))
        .unwrap(),
    )
    .unwrap();
    output
}

#[test]
fn wide_nat_emitted_rust_executes_boundaries_and_real_owned_runtime() {
    let temporary = tempfile::tempdir().unwrap();
    // Optional retention changes only where this test stores its artifacts.
    // It never changes the generated source, commands, assertions or admission.
    let root = std::env::var_os("CLEAN_WIDE_NAT_EXECUTION_RECEIPT")
        .map(PathBuf::from)
        .unwrap_or_else(|| temporary.path().join("fixture"));
    std::fs::create_dir(&root).expect("fresh owned fixture receipt");
    std::fs::create_dir(root.join("src")).unwrap();
    let cases = [
        ("zero", IRLiteral::NatBig(0), vec![]),
        ("small", IRLiteral::NatBig(17), vec![17]),
        (
            "one_word_heap",
            IRLiteral::NatBig(u64::MAX as u128),
            vec![u64::MAX],
        ),
        ("two_words", IRLiteral::NatBig(u128::MAX), vec![u64::MAX; 2]),
        (
            "boundary_128",
            IRLiteral::NatLimbs(vec![0, 0, 1]),
            vec![0, 0, 1],
        ),
        (
            "wide_sparse",
            IRLiteral::NatLimbs(vec![19, 1, 0, 1]),
            vec![19, 1, 0, 1],
        ),
        (
            "many_words",
            IRLiteral::NatLimbs(vec![u64::MAX; 2048]),
            vec![u64::MAX; 2048],
        ),
    ];
    let declarations = cases
        .iter()
        .map(|(label, literal, _)| IRDecl {
            name: Name::from_string(&format!("wide_{label}")),
            params: vec![],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(0),
                ty: IRType::Object,
                value: IRExpr::Lit(literal.clone()),
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            },
        })
        .collect::<Vec<_>>();
    let mut source = clean_compiler::emit_rust::emit_rust(&declarations).unwrap();
    source.push_str(r#"
extern "C" fn keep(first: *mut CleanObj, second: *mut CleanObj) -> *mut CleanObj {
    clean_dec(second);
    first
}
static FOREIGN: CleanExternalClass = CleanExternalClass { finalize: None, foreach: None };
fn main() { unsafe {
    clean_runtime_init();
    match std::env::args().nth(1).as_deref() {
        Some("--reject-string") => { let _ = clean_nat_to_limbs(clean_mk_string("not Nat")); }
        Some("--reject-foreign") => { let _ = clean_nat_to_limbs(clean_alloc_external(&FOREIGN, std::ptr::null_mut())); }
        _ => {}
    }
"#);
    for (label, _, words) in &cases {
        let called =
            clean_compiler::mangle::mangle_name(&Name::from_string(&format!("wide_{label}")));
        let expected = format!("vec!{:?}", words);
        source.push_str(&format!(
            r#"
    {{
        let expected: Vec<u64> = {expected};
        let value = {called}();
        assert_eq!(clean_nat_to_limbs(value), expected);
        assert_eq!(clean_unbox_uint64(value), expected.first().copied().unwrap_or(0));
        assert_eq!(clean_unbox_uint32(value), expected.first().copied().unwrap_or(0) as u32);
        clean_inc(value);
        let shifted = clean_nat_limb_step(value, 9);
        assert_eq!(clean_nat_to_limbs(value), expected);
        clean_dec(value);
        let mut wanted = vec![9]; wanted.extend(expected);
        assert_eq!(clean_nat_to_limbs(shifted), wanted);
        let parent = clean_alloc_ctor(0, 1, 0, &[shifted]);
        let retained = clean_ctor_get(parent, 0); clean_inc(retained); clean_dec(parent);
        assert_eq!(clean_nat_to_limbs(retained), wanted);
        let closure = clean_alloc_closure(keep as *const (), 2, &[retained]); clean_dec(closure);
        println!("{label}:ok");
    }}
"#
        ));
    }
    source.push_str("    clean_runtime_finalize();\n}}\n");
    std::fs::write(root.join("src/main.rs"), source).unwrap();
    let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime");
    std::fs::write(root.join("Cargo.toml"), format!(
        "[package]\nname=\"clean-wide-nat-rust-control\"\nversion=\"0.1.0\"\nedition=\"2021\"\n[workspace]\n[dependencies]\nclean-runtime={{path={:?}}}\n", runtime,
    )).unwrap();
    let driver = std::env::var_os("CARGO").unwrap_or_else(|| "targo".into());
    // Preserve repository cwd/config. Only this new fixture's target is owned.
    let mut lock = Command::new(&driver);
    lock.args(["generate-lockfile", "--offline", "--manifest-path"])
        .arg(root.join("Cargo.toml"));
    let output = capture(lock, &root, "lock");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut build = Command::new(&driver);
    build
        .args([
            "--unverified",
            "build",
            "--locked",
            "--offline",
            "--message-format=json-render-diagnostics",
            "--manifest-path",
        ])
        .arg(root.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(root.join("target"));
    let output = capture(build, &root, "build");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let images = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let value: serde_json::Value = serde_json::from_str(line).ok()?;
            (value["reason"] == "compiler-artifact"
                && value["target"]["name"] == "clean-wide-nat-rust-control")
                .then(|| value["executable"].as_str().map(PathBuf::from))
                .flatten()
        })
        .collect::<Vec<_>>();
    assert_eq!(images.len(), 1, "one actual Cargo-selected executable");
    let image = &images[0];
    std::fs::write(
        root.join("SELECTED_IMAGE.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "path": image,
        "postbuild_bytes": std::fs::metadata(image).unwrap().len(),
            "scope": "actual Cargo-selected control image; no before-build compiled closure claim",
        }))
        .unwrap(),
    )
    .unwrap();
    let output = capture(Command::new(image), &root, "positive");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let actual = String::from_utf8(output.stdout).unwrap();
    assert_eq!(
        actual.lines().map(str::to_owned).collect::<Vec<_>>(),
        cases
            .iter()
            .map(|(label, _, _)| format!("{label}:ok"))
            .collect::<Vec<_>>()
    );
    for (argument, diagnostic) in [
        ("--reject-string", "invalid Rust Nat carrier"),
        ("--reject-foreign", "invalid Rust Nat external class"),
    ] {
        let mut command = Command::new(image);
        command.arg(argument);
        let output = capture(command, &root, argument.trim_start_matches("--"));
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains(diagnostic));
    }
}
