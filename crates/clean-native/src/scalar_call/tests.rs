// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use clean_kernel::env::TrustedEnvExt;

const SOURCE: &str = "def scalar (a b : UInt32) (c d : UInt64) : UInt64 :=\n\
  a.toUInt64 + b.toUInt64 * 65537 + c * 3 + d * 5\n\
def heap (a b : UInt32) (c d : UInt64) : UInt64 :=\n\
  UInt64.ofNat (c.toNat + d.toNat + a.toNat + b.toNat)\n\
def wrong (a : UInt64) (b : UInt32) (c d : UInt64) : UInt64 := c\n\
def short (a b : UInt32) (c : UInt64) : UInt64 := c\n\
def result (a b : UInt32) (c d : UInt64) : UInt32 := a\n\
def malloc (a b : UInt32) (c d : UInt64) : UInt64 :=\n\
  a.toUInt64 + b.toUInt64 + c + d\n";

#[test]
fn source_signature_and_transitive_primitive_forgery_refuse() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("Scalar.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let env = crate::compile::elaborate_file_to_env(&file).unwrap();
    source_contract(&env, &Name::from_string("scalar")).unwrap();
    for name in ["wrong", "short", "result"] {
        let error = source_contract(&env, &Name::from_string(name)).unwrap_err();
        assert!(
            error.to_string().contains("scalar source type refused"),
            "{error:#}"
        );
    }
    for name in ["UInt32", "UInt64", "BitVec"] {
        let mut forged = env.clone();
        let n = Name::from_string(name);
        let mut info = forged.get_const(&n).unwrap().clone();
        // Explicitly untrusted test-only record substitution. Keeping the
        // primitive Name must not create source/ABI authority.
        info.value = Some(Expr::const_str("Nat"));
        forged.forget_decl(&n);
        assert!(forged
            .extend_constants_structural(std::iter::once(info))
            .is_empty());
        let error = source_contract(&forged, &Name::from_string("scalar")).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("noncanonical scalar primitive/layout"),
            "{name}: {error:#}"
        );
    }
    for name in [
        "UInt32.ofBitVec",
        "UInt64.ofBitVec",
        "UInt32.toBitVec",
        "UInt64.toBitVec",
        "Fin.val",
    ] {
        let n = Name::from_string(name);
        assert!(
            env.get_const(&n).is_some(),
            "actual canonical primitive/projection must exist"
        );
        for implementation in [false, true] {
            let mut forged = env.clone();
            if implementation {
                forged.register_implemented_by(n.clone(), Name::from_string("scalar"));
            } else {
                forged.register_extern(n.clone(), "noncanonical_runtime_symbol".to_owned());
            }
            assert_eq!(
                forged.get_const(&n),
                env.get_const(&n),
                "typed record intentionally unchanged"
            );
            let error = source_contract(&forged, &Name::from_string("scalar")).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("noncanonical scalar primitive/layout"),
                "{name}: {error:#}"
            );
        }
    }
    for unsafe_ in [false, true] {
        let mut marked = env.clone();
        let root = Name::from_string("scalar");
        if unsafe_ {
            marked.mark_unsafe(root.clone());
        } else {
            marked.mark_partial(root.clone());
        }
        let error = source_contract(&marked, &root).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("scalar source eligibility refused"),
            "{error:#}"
        );
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn real_source_object_runtime_loaded_scalar_calls_preserve_widths_order_and_lifetime() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("Scalar.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let vectors = [
        (0, 0, 0, 0),
        (1, 2, 3, 4),
        (u32::MAX, 0, 0, 1),
        (0, u32::MAX, 1u64 << 63, 7),
        (0x8000_0001, 0x1234_5678, u64::MAX, u64::MAX - 13),
    ];
    let mut calls = 0;
    for opt_level in [0, 2] {
        let mut scalar = ScalarCall::from_source(&file, "scalar", opt_level)
            .unwrap_or_else(|e| panic!("actual object/runtime/loader O{opt_level}: {e:#}"));
        capture(&scalar, &file, opt_level, "scalar");
        let owned_image = scalar._scratch.path().to_path_buf();
        assert_eq!(scalar.declaration(), &Name::from_string("scalar"));
        for (a, b, c, d) in vectors {
            let expected = u64::from(a)
                .wrapping_add(u64::from(b).wrapping_mul(65537))
                .wrapping_add(c.wrapping_mul(3))
                .wrapping_add(d.wrapping_mul(5));
            assert_eq!(
                scalar.call(a, b, c, d),
                expected,
                "O{opt_level}: {:?}",
                (a, b, c, d)
            );
            calls += 1;
        }
        for i in 0..256u64 {
            let a = (i.wrapping_mul(0x8123_4567)) as u32;
            let b = (i.wrapping_mul(0x7654_3211).wrapping_add(17)) as u32;
            let c = i.wrapping_mul(0x9234_5678_9abc_def1);
            let d = i.wrapping_mul(0x1357_9bdf_2468_ace1).wrapping_add(31);
            let expected = u64::from(a)
                .wrapping_add(u64::from(b).wrapping_mul(65537))
                .wrapping_add(c.wrapping_mul(3))
                .wrapping_add(d.wrapping_mul(5));
            assert_eq!(scalar.call(a, b, c, d), expected, "O{opt_level} vector {i}");
            calls += 1;
        }
        assert!(owned_image.join("scalar.dylib").is_file());
        let mut heap = ScalarCall::from_source(&file, "heap", opt_level)
            .unwrap_or_else(|e| panic!("actual managed internal runtime O{opt_level}: {e:#}"));
        capture(&heap, &file, opt_level, "heap");
        for (a, b, c, d) in vectors {
            let expected = c
                .wrapping_add(d)
                .wrapping_add(u64::from(a))
                .wrapping_add(u64::from(b));
            // Repeated calls stay in one loaded image. Values above 2^63 and
            // 2^64 exercise the complete runtime's heap Nat path internally.
            for _ in 0..32 {
                assert_eq!(heap.call(a, b, c, d), expected, "heap O{opt_level}");
                calls += 1;
            }
        }
        assert_eq!(
            scalar.call(1, 2, 3, 4),
            131104,
            "other loaded image must retain its own body"
        );
        calls += 1;
        let heap_image = heap._scratch.path().to_path_buf();
        assert_ne!(heap_image, owned_image);
        drop(heap);
        assert!(!heap_image.exists());
        assert!(owned_image.join("scalar.dylib").is_file());
        assert_eq!(
            scalar.call(9, 8, 7, 6),
            524356,
            "dropping another image must preserve this callable"
        );
        calls += 1;
        drop(scalar);
        assert!(
            !owned_image.exists(),
            "files removed after releasing the owned loader reference"
        );
    }
    let error = match ScalarCall::from_source(&file, "malloc", 0) {
        Err(error) => error,
        Ok(_) => panic!("source definition must not capture the complete runtime's malloc import"),
    };
    assert!(
        error
            .to_string()
            .contains("source/runtime link symbol collision")
            && error.to_string().contains("malloc"),
        "{error:#}"
    );
    assert_eq!(calls, 846);
    eprintln!("actual direct scalar calls: {calls}; four simultaneous-lifetime-controlled loaded images; one actual-runtime-symbol collision refused; Clean pipeline levels0,2; compiler unvalidated, no model claim");
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn capture(call: &ScalarCall, source: &Path, opt_level: u8, name: &str) {
    if let Some(output) = std::env::var_os("CLEAN_SCALAR_NATIVE_CAPTURE") {
        let output = std::path::PathBuf::from(output).join(format!("{name}-O{opt_level}"));
        std::fs::create_dir_all(&output).unwrap();
        for name in [
            "source.o",
            "scalar.dylib",
            "scalar_bridge.c",
            "scalar-symbols.json",
            "clean_runtime.h",
            "clean_runtime.c",
            "runtime_extern.c",
            "clean_prelude_shims.c",
            "clean_runtime.o",
            "runtime_extern.o",
            "clean_prelude_shims.o",
            "libclean_runtime.a",
        ] {
            std::fs::copy(call._scratch.path().join(name), output.join(name)).unwrap();
        }
        std::fs::copy(source, output.join("Scalar.lean")).unwrap();
    }
}

fn replay_fixture() -> (
    std::sync::Arc<Environment>,
    std::sync::Arc<Environment>,
    BTreeSet<Name>,
    clean_olean::ReplayedImportedSource,
) {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("Replayed.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let mut source = crate::compile::elaborate_file_to_env(&file).unwrap();
    assert!(source.set_constant_origin(
        Name::from_string("scalar"),
        clean_kernel::ConstantOrigin::olean_import(Some("Replayed".into()))
    ));
    let base = std::sync::Arc::new(Environment::with_prelude());
    let source = std::sync::Arc::new(source);
    let mut roots = scalar_source_roots().unwrap();
    roots.insert(Name::from_string("scalar"));
    let replay = clean_olean::ReplayedImportedSource::check(
        std::sync::Arc::clone(&base),
        std::sync::Arc::clone(&source),
        roots.clone(),
    )
    .unwrap();
    (base, source, roots, replay)
}
#[test]
fn scalar_replayed_source_uses_actual_proof_without_changing_original_origin() {
    let (base, source, roots, replay) = replay_fixture();
    let root = Name::from_string("scalar");
    assert!(source.constant_needs_recheck(&root));
    assert!(source_contract(&source, &root).is_err());
    replay.require_context(&base, &source, &roots).unwrap();
    source_contract_with_replay(&source, &root, Some(&replay)).unwrap();
    assert!(source.constant_needs_recheck(&root));
}
#[test]
fn scalar_replayed_source_preserves_original_flags_and_primitive_layout() {
    let (_base, source, _roots, replay) = replay_fixture();
    for primitive in ["UInt32", "UInt64", "BitVec"] {
        let mut changed = (*source).clone();
        let name = Name::from_string(primitive);
        let mut info = changed.get_const(&name).unwrap().clone();
        info.value = Some(Expr::const_str("Nat"));
        changed.forget_decl(&name);
        assert!(changed
            .extend_constants_structural(std::iter::once(info))
            .is_empty());
        assert!(
            source_contract_with_replay(&changed, &Name::from_string("scalar"), Some(&replay))
                .is_err()
        );
    }
    for partial in [false, true] {
        let mut changed = (*source).clone();
        if partial {
            changed.mark_partial(Name::from_string("scalar"));
        } else {
            changed.mark_unsafe(Name::from_string("scalar"));
        }
        assert!(
            source_contract_with_replay(&changed, &Name::from_string("scalar"), Some(&replay))
                .is_err()
        );
    }
}

#[test]
fn scalar_replayed_source_fresh_unsafe_and_partial_originals_refuse() {
    for marker in ["unsafe", "partial"] {
        let (base, source, roots, _earlier) = replay_fixture();
        let root = Name::from_string("scalar");
        let mut original = (*source).clone();
        if marker == "unsafe" {
            original.mark_unsafe(root.clone());
        } else {
            original.mark_partial(root.clone());
        }
        let error =
            clean_olean::ReplayedImportedSource::check(base, std::sync::Arc::new(original), roots)
                .unwrap_err();
        let clean_olean::ReplayedSourceError::Replay(_, verdict) = error else {
            panic!("expected actual fresh replay refusal for {marker}: {error:?}");
        };
        assert!(
            verdict.refusals.iter().any(|refusal| matches!(
                refusal,
                clean_olean::ClosedRecheckRefusal::OutsideTrustedFragment { name, marker: found }
                    if name == "scalar" && *found == marker
            )),
            "{marker}: {verdict:?}"
        );
    }
}

#[test]
fn scalar_replayed_source_fresh_staged_original_cannot_borrow_replay_eligibility() {
    let (base, source, roots, _earlier) = replay_fixture();
    let root = Name::from_string("scalar");
    let mut original = (*source).clone();
    let info = original.get_const(&root).unwrap().clone();
    original.forget_decl(&root);
    original
        .add_staged_header(clean_kernel::Declaration::Axiom {
            name: root.clone(),
            level_params: info.level_params,
            type_: info.type_,
        })
        .unwrap();
    assert!(original.is_staged_header(&root));
    let original = std::sync::Arc::new(original);
    let error =
        clean_olean::ReplayedImportedSource::check(base, std::sync::Arc::clone(&original), roots)
            .unwrap_err();
    let clean_olean::ReplayedSourceError::Replay(_, verdict) = error else {
        panic!("expected actual staged-source replay refusal: {error:?}");
    };
    assert_eq!(verdict.imported_axioms, vec!["scalar"]);
    assert!(!verdict.passed(false));
    let error = source_contract(&original, &root).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("scalar source eligibility refused"),
        "{error:#}"
    );
    assert!(original.is_staged_header(&root));
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn scalar_replayed_source_actual_call_retains_original_pending_origin() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("ReplayedCall.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let args = CompileArgs {
        file: Some(file.clone()),
        decl: Some("scalar".into()),
        emit: EmitFormat::Obj,
        opt_level: 0,
        output: None,
        link_artifact: vec![],
    };
    let (decls, mut env, pipeline) = crate::compile::select_lcnf_decl(&args).unwrap();
    let root = Name::from_string("scalar");
    assert!(env.set_constant_origin(
        root.clone(),
        clean_kernel::ConstantOrigin::olean_import(Some("ReplayedCall".into()))
    ));
    let source = std::sync::Arc::new(env);
    let base = std::sync::Arc::new(Environment::with_prelude());
    let mut roots = scalar_source_roots().unwrap();
    roots.insert(root.clone());
    roots.extend(
        decls
            .iter()
            .filter(|d| source.get_const(&d.name).is_some())
            .map(|d| d.name.clone()),
    );
    let replay = clean_olean::ReplayedImportedSource::check(
        std::sync::Arc::clone(&base),
        std::sync::Arc::clone(&source),
        roots.clone(),
    )
    .unwrap();
    replay.require_context(&base, &source, &roots).unwrap();
    assert!(source.constant_needs_recheck(&root));
    let mut call = ScalarCall::from_selected_with_replay(
        &decls,
        &source,
        &pipeline,
        &root,
        Some(&file),
        None,
        Some(&replay),
    )
    .unwrap();
    capture(&call, &file, 0, "replayed-scalar");
    let cases: [(u32, u32, u64, u64); 3] =
        [(0, 0, 0, 0), (u32::MAX, 1, u64::MAX, 0), (7, 11, 13, 17)];
    for (a, b, c, d) in cases {
        let expected = u64::from(a)
            .wrapping_add(u64::from(b).wrapping_mul(65537))
            .wrapping_add(c.wrapping_mul(3))
            .wrapping_add(d.wrapping_mul(5));
        assert_eq!(call.call(a, b, c, d), expected);
    }
    assert!(source.constant_needs_recheck(&root));
    println!("actual source-bound imported-origin replay -> existing scalar object/runtime/in-process3cases PASS; originalpendingorigin retained");
}
