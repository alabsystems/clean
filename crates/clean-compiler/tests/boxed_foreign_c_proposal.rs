// Copyright 2026 Andrew Yates | Apache-2.0
//! Finite C oracle for an untrusted emitted proposal, not source/ABI/NoUB proof.
use clean_compiler::emit_c::propose_boxed_foreign_c;
use clean_compiler::ffi_bridge::FfiBridge;
use clean_compiler::lcnf::{ExternAttr, ExternEntry, Param};
use clean_kernel::{Expr, FVarId, Name};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn include() -> PathBuf {
    std::env::var_os("CLEAN_TEST_LEAN_INCLUDE")
        .map(PathBuf::from)
        .or_else(|| {
            clean_olean::pinned_lean_lib_path()
                .and_then(|lib| Some(lib.parent()?.parent()?.join("include")))
        })
        .expect("actual repository-pinned Lean include DATA is required")
}

fn bridge() -> FfiBridge {
    let ty = Expr::const_str("UInt64");
    let params = [
        Param::new(FVarId::new(0), Name::from_string("left"), ty.clone()),
        Param::new(FVarId::new(1), Name::from_string("right"), ty.clone()),
    ];
    let add = Name::from_string("UInt64.add");
    let mul = Name::from_string("UInt64.mul");
    let add_attr = ExternAttr {
        entries: vec![ExternEntry {
            backend: "c".into(),
            name: "lean_uint64_add".into(),
        }],
    };
    let mul_attr = ExternAttr {
        entries: vec![ExternEntry {
            backend: "c".into(),
            name: "lean_uint64_mul".into(),
        }],
    };
    FfiBridge::from_lcnf_externs(&[
        (add, &params, &ty, &add_attr),
        (mul, &params, &ty, &mul_attr),
    ])
}

fn compile(root: &Path, lean_include: &Path, owner: bool, output: &Path) -> Output {
    let mut cc = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
    cc.args(["-std=c11", "-O0", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(lean_include)
        .arg("-I")
        .arg(root.join("include"))
        .arg(root.join("driver.c"))
        .arg(root.join("src/clean_runtime.c"));
    if owner {
        cc.arg(root.join("owner.c"));
    }
    cc.arg("-o")
        .arg(output)
        .output()
        .expect("C oracle compiler")
}

#[test]
fn test_emitted_boxed_entries_call_real_header_owners_including_two_owned_aliases() {
    let include = include();
    let header_before = std::fs::read(include.join("lean/lean.h")).unwrap();
    let bridge = bridge();
    let proposal = propose_boxed_foreign_c(
        &bridge,
        &[
            Name::from_string("UInt64.add"),
            Name::from_string("UInt64.mul"),
        ],
    )
    .unwrap();
    assert_eq!(proposal.entries.len(), 2);
    let directory = tempfile::tempdir().unwrap();
    // Retain the actual emitted source and linked controls, including on panic.
    // These are finite oracle DATA, never a source/ABI correctness certificate.
    let retained = directory.keep();
    eprintln!("boxed foreign C oracle DATA: {}", retained.display());
    let root = retained.as_path();
    std::fs::create_dir(root.join("include")).unwrap();
    std::fs::create_dir(root.join("src")).unwrap();
    std::fs::write(
        root.join("include/clean_runtime.h"),
        clean_runtime::runtime_header(),
    )
    .unwrap();
    std::fs::write(
        root.join("src/clean_runtime.c"),
        clean_runtime::runtime_source(),
    )
    .unwrap();
    let owner = clean_runtime::lean_word64_extern_source();
    std::fs::write(root.join("owner.c"), owner).unwrap();
    std::fs::write(root.join("owner-original.c"), owner).unwrap();
    let driver = format!(
        r#"
{code}
_Static_assert(_Generic(&{add}, clean_obj* (*)(clean_obj*,clean_obj*): 1, default: 0), "boxed add signature");
_Static_assert(_Generic(&{mul}, clean_obj* (*)(clean_obj*,clean_obj*): 1, default: 0), "boxed mul signature");
_Static_assert(sizeof(clean_obj_header) == 8, "retained runtime header");
_Static_assert(offsetof(clean_obj, fields) == 8, "retained payload offset");
int main(void) {{
  const uint64_t values[] = {{0,1,2,3,UINT64_C(0x7fffffffffffffff), UINT64_C(0x8000000000000000),UINT64_MAX-1,UINT64_MAX}};
  for (size_t op=0; op<2; ++op) {{
    void* entry = op ? (void*){mul} : (void*){add};
    for (size_t a=0; a<8; ++a) for (size_t b=0; b<8; ++b) {{
      clean_obj* fn = clean_alloc_closure(entry,2,0);
      clean_obj* result = clean_apply_2(fn,clean_box_uint64(values[a]),clean_box_uint64(values[b]));
      uint64_t expected = op ? values[a]*values[b] : values[a]+values[b];
      if (clean_unbox_uint64(result) != expected) return op ? 12 : 11;
      clean_dec(result);
    }}
    for (size_t a=0; a<8; ++a) {{
      clean_obj* shared = clean_box_uint64(values[a]);
      if (atomic_load_explicit(&shared->header.ref_count,memory_order_relaxed) != 0) return 20;
      clean_inc(shared); /* TWO owned references to the SAME pointer. */
      if (atomic_load_explicit(&shared->header.ref_count,memory_order_relaxed) != 1) return 21;
      clean_obj* result = clean_apply_2(clean_alloc_closure(entry,2,0),shared,shared);
      uint64_t expected = op ? values[a]*values[a] : values[a]+values[a];
      if (clean_unbox_uint64(result) != expected) return op ? 14 : 13;
      clean_dec(result);
    }}
  }}
  const uint32_t smalls[] = {{0,1,UINT32_C(0x7fffffff),UINT32_C(0x80000000),UINT32_MAX}};
  for (size_t i=0; i<sizeof(smalls)/sizeof(smalls[0]); ++i) {{
    clean_obj* value = clean_box_uint32(smalls[i]);
    if (clean_unbox_uint32(value) != smalls[i]) return 13;
#if SIZE_MAX > UINT32_MAX
    if (!clean_is_scalar(value)) return 14;
#endif
    clean_dec(value);
  }}
  return 0;
}}
"#,
        code = proposal.code,
        add = proposal.entries[0].boxed_symbol,
        mul = proposal.entries[1].boxed_symbol
    );
    std::fs::write(root.join("driver.c"), &driver).unwrap();
    let missing = compile(root, &include, false, &root.join("absent"));
    assert!(!missing.status.success());
    let error = String::from_utf8_lossy(&missing.stderr);
    assert!(
        error.contains("lean_uint64_add") && error.contains("lean_uint64_mul"),
        "{error}"
    );
    let good = root.join("good");
    let built = compile(root, &include, true, &good);
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    assert!(Command::new(&good).status().unwrap().success());
    for (operation, exit) in [("add", 11), ("mul", 12)] {
        let from = format!("return lean_uint64_{operation}__clean_header_owner(left, right);");
        let to = format!(
            "return lean_uint64_{operation}__clean_header_owner(left, right) ^ UINT64_C(1);"
        );
        let changed = owner.replace(&from, &to);
        assert_ne!(changed, owner);
        std::fs::write(root.join(format!("owner-mutant-{operation}.c")), &changed).unwrap();
        std::fs::write(root.join("owner.c"), changed).unwrap();
        let mutant = root.join(format!("changed-{operation}"));
        let built = compile(root, &include, true, &mutant);
        assert!(
            built.status.success(),
            "{}",
            String::from_utf8_lossy(&built.stderr)
        );
        assert_eq!(Command::new(mutant).status().unwrap().code(), Some(exit));
    }
    assert_eq!(
        std::fs::read(include.join("lean/lean.h")).unwrap(),
        header_before
    );
}
