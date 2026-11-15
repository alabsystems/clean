// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{BinderInfo, ConstantInfo, Expr};

const SOURCE: &str = "prelude\nimport Target\n\
inductive Flag where\n  | off\n  | on\n\
structure Pair where\n  left : Flag\n  right : Leaf\n\
private structure RequestMetadata where\n  request : Pair\n\
def recorded : RequestMetadata := RequestMetadata.mk (Pair.mk Flag.on targetVal)\n\
def keep (p : Pair) : Pair := p\n\
def applyLeaf (f : Leaf → Flag) (x : Leaf) : Flag := f x\n\
def recordLeaf (x : Flag) : Pair := Pair.mk x targetVal\n\
def handoff (x : Flag) : Flag := applyLeaf (fun _ => (keep (recordLeaf x)).left) targetVal\n\
inductive Claim : Prop where\n  | intro\n\
theorem sound : Claim := Claim.intro\n\
axiom foreign : Leaf\n\
noncomputable def usesForeign : Leaf := foreign\n\
@[extern \"absent_external_leaf\"] def externLeaf (x : Leaf) : Leaf := x\n\
def ffiCaller : Leaf := externLeaf targetVal\n\
def fast (x : Leaf) : Leaf := x\n\
@[implemented_by fast] def slow (x : Leaf) : Leaf := targetVal\n\
def routed : Leaf := slow targetVal\n\
unsafe def unsafeLeaf (x : Leaf) : Leaf := x\n";

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.30.0/closure_cache")
}

fn program(source: &str) -> ExternalLeanProgram {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Handoff.lean");
    program_at(&file, source)
}

fn program_at(file: &Path, source: &str) -> ExternalLeanProgram {
    std::fs::write(file, source).unwrap();
    ExternalLeanProgram::elaborate(ExternalLeanInput {
        file,
        module: &Name::from_string("Handoff"),
        imports: &[Name::from_string("Target")],
        search_paths: &[fixture()],
        world: LeanWorld::ORACLE,
    })
    .unwrap_or_else(|e| panic!("actual official Lean handoff: {e}"))
}

fn n(name: &str) -> Name {
    Name::from_string(name)
}

#[test]
fn actual_imported_leaf_context_reaches_existing_native_compiler() {
    let program = program(SOURCE);
    assert_eq!(program.world(), LeanWorld::ORACLE);
    assert_eq!(program.source_capture().sources[0].source, SOURCE);
    assert!(program.source_capture().snapshot_blake3.is_some());
    assert!(program
        .inputs()
        .iter()
        .any(|r| r.path.ends_with("Target.olean")));
    let selected = program.select(&n("handoff"), 0).unwrap();
    assert!(selected.replay_verdict().passed(false));
    assert!(selected.replay_verdict().constants_admitted > 0);
    assert!(selected.replay_verdict().families_replayed > 0);
    assert_ne!(selected.closure_digest(), [0; 32]);
    let c = selected.emit(EmitFormat::C).unwrap();
    let build = tempfile::tempdir().unwrap();
    let binary = crate::native_build::build_extract_executable(build.path(), "", &c,
        "int main(void) { for (unsigned tag = 0; tag < 2; ++tag) { clean_obj* result = l_handoff(clean_box(tag)); if (clean_obj_tag(result) != tag) return 1; } return 0; }")
        .unwrap_or_else(|e| panic!("existing native build: {e:#}\n{c}"));
    let status = Command::new(binary).status().unwrap();
    assert!(
        status.success(),
        "actual imported record/function/closure program: {status}"
    );
}

#[test]
fn imported_library_name_cannot_be_selected_as_source_declaration() {
    let program = program(SOURCE);
    let error = match program.select(&n("targetVal"), 0) {
        Err(e) => e,
        Ok(_) => panic!("wrong selected declaration accepted"),
    };
    assert!(error
        .to_string()
        .contains("not declared by the captured source module"));
}

#[test]
fn imported_axioms_and_existing_ffi_policy_remain_refusals() {
    let program = program(SOURCE);
    let error = match program.select(&n("usesForeign"), 0) {
        Err(e) => e,
        Ok(_) => panic!("imported axiom accepted"),
    };
    assert!(error.to_string().contains("foreign"), "{error}");
    assert!(
        matches!(&error, ExternalLeanError::Replay { verdict, .. } if verdict.imported_axioms.iter().any(|name| name == "foreign")),
        "the actual axiom scan remains available, not only its rendered error"
    );
    let error = match program.select(&n("ffiCaller"), 0) {
        Err(e) => e,
        Ok(_) => panic!("extern body accepted"),
    };
    assert!(error.to_string().contains("native-extern-body"), "{error}");
}

fn replace(program: &mut ExternalLeanProgram, name: &str, mutate: impl FnOnce(&mut ConstantInfo)) {
    let name = n(name);
    let mut info = program.env.get_const(&name).unwrap().clone();
    mutate(&mut info);
    program.env.forget_decl(&name);
    // SOUNDNESS: test-only import forgery; the production handoff has no
    // caller-accessible environment mutator. Replay must refuse the payload.
    let rejected = program
        .env
        .extend_constants_structural(std::iter::once(info));
    assert!(rejected.is_empty());
}

#[test]
fn modified_imported_proof_and_type_are_replayed_before_compilation() {
    for field in ["proof", "type"] {
        let mut program = program(SOURCE);
        replace(&mut program, "sound", |info| match field {
            "proof" => {
                info.value = Some(Expr::lam(
                    BinderInfo::Default,
                    Expr::const_(n("Leaf"), vec![]),
                    Expr::bvar(0),
                ))
            }
            _ => info.type_ = Expr::sort(clean_kernel::Level::zero()),
        });
        let error = match program.select(&n("sound"), 0) {
            Err(e) => e,
            Ok(_) => panic!("modified {field} accepted"),
        };
        assert!(
            matches!(error, ExternalLeanError::Replay { .. }),
            "{field}: {error}"
        );
    }
}

#[test]
fn mixed_world_imports_and_source_bookends_refuse() {
    let dir = tempfile::tempdir().unwrap();
    let source = dir.path().join("Handoff.lean");
    std::fs::write(&source, "prelude\nimport Minimal\n").unwrap();
    let historical =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.13.0/custom");
    let result = ExternalLeanProgram::elaborate(ExternalLeanInput {
        file: &source,
        module: &n("Handoff"),
        imports: &[n("Minimal")],
        search_paths: &[historical],
        world: LeanWorld::ORACLE,
    });
    let error = match result {
        Err(e) => e,
        Ok(_) => panic!("mixed world accepted"),
    };
    assert!(error.to_string().contains("world"), "{error}");
    let mut files = snapshot::Files::default();
    files.observe(&source).unwrap();
    std::fs::write(&source, "changed source").unwrap();
    assert!(
        files.check().is_err(),
        "changed source must invalidate custody"
    );
}

#[test]
fn modified_imported_constructor_mirror_is_refused() {
    let mut program = program(SOURCE);
    replace(&mut program, "Pair.mk", |info| {
        info.type_ = Expr::const_(n("Leaf"), vec![])
    });
    let error = match program.select(&n("handoff"), 0) {
        Err(e) => e,
        Ok(_) => panic!("modified constructor accepted"),
    };
    assert!(matches!(error, ExternalLeanError::Replay { .. }), "{error}");
}

#[test]
fn omitted_actual_import_never_mints_an_external_program() {
    let dir = tempfile::tempdir().unwrap();
    let source = dir.path().join("Handoff.lean");
    std::fs::write(&source, SOURCE).unwrap();
    let result = ExternalLeanProgram::elaborate(ExternalLeanInput {
        file: &source,
        module: &n("Handoff"),
        imports: &[],
        search_paths: &[fixture()],
        world: LeanWorld::ORACLE,
    });
    assert!(result.is_err(), "uncaptured actual source import accepted");
}

#[test]
fn implemented_by_runtime_body_is_replayed_and_selected_by_existing_policy() {
    let program = program(SOURCE);
    let selected = program.select(&n("routed"), 0).unwrap();
    assert!(selected
        .declarations()
        .iter()
        .any(|decl| decl.name == n("fast")));
    assert!(!selected
        .declarations()
        .iter()
        .any(|decl| decl.name == n("slow")));
    assert!(selected.replay_verdict().passed(false));
    assert!(selected.runtime_replay_verdict().passed(false));
    assert!(selected
        .runtime_replay_verdict()
        .roots
        .iter()
        .any(|root| root == "fast"));
    assert!(
        program.select(&n("slow"), 0).is_err(),
        "root implemented_by policy bypassed"
    );
    assert!(
        program.select(&n("unsafeLeaf"), 0).is_err(),
        "unsafe root eligibility bypassed"
    );
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn actual_imported_record_closure_reaches_extern_calls_and_checked_object_path() {
    let program = program(SOURCE);
    let selected = program.select(&n("handoff"), 0).unwrap();
    let ir = selected
        .emit(EmitFormat::Trustir)
        .unwrap_or_else(|e| panic!("actual ExternCalls lowering refused: {e}"));
    assert!(ir.contains("fn @handoff("), "{ir}");
    assert!(ir.contains("fn @clean_alloc_ctor("), "{ir}");
    assert!(ir.contains("fn @clean_alloc_closure("), "{ir}");
    let dir = tempfile::tempdir().unwrap();
    let object = dir.path().join("handoff.o");
    selected
        .emit_object(&object)
        .unwrap_or_else(|e| panic!("maintained checked native-object path refused: {e}"));
    assert!(object.metadata().unwrap().len() > 0);
    // Link the actual TrustCG object to the maintained complete runtime
    // archive. This driver independently observes both source flag values.
    crate::native_runtime::materialize(dir.path(), false, &mut Vec::new()).unwrap();
    let driver = dir.path().join("driver.c");
    std::fs::write(&driver, "#include \"clean_runtime.h\"\nextern clean_obj* handoff(clean_obj*);\nint main(void) { for (unsigned tag = 0; tag < 2; ++tag) { clean_obj* result = handoff(clean_box(tag)); if (clean_obj_tag(result) != tag) return 1; } return 0; }\n").unwrap();
    let binary = dir.path().join("native-program");
    let cc = crate::native_build::find_c_compiler().expect("actual native C linker required");
    let output = crate::native_c_toolchain::command(&cc)
        .unwrap()
        .args(["-O2", "-std=c11", "-I"])
        .arg(dir.path())
        .arg(&driver)
        .arg(&object)
        .arg(dir.path().join("libclean_runtime.a"))
        .arg("-lm")
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "actual maintained runtime link: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let status = Command::new(&binary).status().unwrap();
    assert!(
        status.success(),
        "actual TrustCG record/closure program: {status}"
    );
    let sha256 = |path: &Path| {
        use sha2::Digest;
        sha2::Sha256::digest(std::fs::read(path).unwrap())
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    };
    eprintln!("external Lean handoff: actual TrustCG object + complete runtime, captured record/closure, 2 flag cases, {status}; clean-compiler-unvalidated; no binary proof");
    eprintln!(
        "executed native artifact SHA256: binary={} object={} runtime={} driver={}",
        sha256(&binary),
        sha256(&object),
        sha256(&dir.path().join("libclean_runtime.a")),
        sha256(&driver),
    );
}

#[test]
fn source_snapshot_identity_changes_with_actual_source_bytes() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("Handoff.lean");
    let original = program_at(&file, SOURCE);
    let modified = SOURCE.replace("(recordLeaf x)", "(recordLeaf Flag.off)");
    assert_ne!(modified, SOURCE);
    let changed = program_at(&file, &modified);
    assert_eq!(original.source_capture().sources[0].source, SOURCE);
    assert_eq!(changed.source_capture().sources[0].source, modified);
    assert_ne!(
        original.source_capture().snapshot_blake3,
        changed.source_capture().snapshot_blake3,
        "different bytes at the same original source path must have different observations"
    );
    assert_ne!(
        original.select(&n("handoff"), 0).unwrap().closure_digest(),
        changed.select(&n("handoff"), 0).unwrap().closure_digest(),
        "the actual changed generated declaration must change its authenticated closure identity"
    );
}

#[test]
fn pure_noncomputable_source_definition_keeps_its_codegen_ineligibility() {
    let source = format!("{SOURCE}\nnoncomputable def noncomputablePure (x : Leaf) : Leaf := x\n");
    let program = program(&source);
    assert!(
        program
            .source_capture()
            .after
            .iter()
            .any(|row| row.name == n("noncomputablePure") && row.noncomputable),
        "the actual Lean noncomputable tag must survive imported-context capture; output extensions: {:?}",
        clean_olean::parse_module_file(program.custody._snapshot.path().join("Handoff.olean")).unwrap()
            .entries.iter().map(|entry| &entry.extension_name).collect::<Vec<_>>()
    );
    let error = match program.select(&n("noncomputablePure"), 0) {
        Err(e) => e,
        Ok(_) => panic!("pure noncomputable declaration bypassed source eligibility"),
    };
    assert!(matches!(error, ExternalLeanError::Compile(_)), "{error}");
}

#[test]
fn typed_owned_metadata_can_be_replayed_and_inspected_without_codegen() {
    let program = program(SOURCE);
    let metadata = program.inspect_owned_declaration(&n("recorded")).unwrap();
    assert_eq!(metadata.constant().name, n("recorded"));
    assert!(metadata.replay_verdict().passed(false));
    let value = metadata.constant().value.as_ref().unwrap();
    let clean_kernel::ExprKind::Const(metadata_type, _) = metadata.constant().type_.kind() else {
        panic!("metadata must retain its actual constructor-family type");
    };
    assert_ne!(
        metadata_type,
        &n("RequestMetadata"),
        "the metadata family has its actual private Lean identity"
    );
    assert!(
        matches!(value.get_app_fn().kind(), clean_kernel::ExprKind::Const(name, _) if *name == metadata_type.clone().str("mk"))
    );
    assert_ne!(metadata.closure_digest(), [0; 32]);
    assert!(
        program.inspect_owned_declaration(&n("targetVal")).is_err(),
        "an imported declaration is not source-owned metadata"
    );
    let proof = program.inspect_owned_declaration(&n("sound")).unwrap();
    assert!(proof.replay_verdict().passed(false));
    assert!(proof.constant().value.is_some());
}

#[cfg(unix)]
#[test]
fn dangling_import_companion_is_refused_instead_of_copied_as_absent() {
    let dir = tempfile::tempdir().unwrap();
    for module in ["Init", "Target"] {
        std::fs::copy(
            fixture().join(format!("{module}.olean")),
            dir.path().join(format!("{module}.olean")),
        )
        .unwrap();
    }
    let companion = dir.path().join("Target.olean.private");
    let mut files = snapshot::Files::default();
    files.absent(&companion);
    std::os::unix::fs::symlink(dir.path().join("missing-private"), &companion).unwrap();
    assert!(
        files.check().is_err(),
        "even an unreadable new companion breaks the absence bookend"
    );
    let source = dir.path().join("Handoff.lean");
    std::fs::write(
        &source,
        "prelude\nimport Target\ndef handoff := targetVal\n",
    )
    .unwrap();
    let result = ExternalLeanProgram::elaborate(ExternalLeanInput {
        file: &source,
        module: &n("Handoff"),
        imports: &[n("Target")],
        search_paths: &[dir.path().to_path_buf()],
        world: LeanWorld::ORACLE,
    });
    assert!(
        matches!(result, Err(ExternalLeanError::Io(_))),
        "a dangling companion must preserve the existing unreadable-artifact refusal"
    );
}

#[path = "runtime_binding_tests.rs"]
mod runtime_binding;
