// Copyright 2026 Andrew Yates | Apache-2.0
//! Link/oracle controls only: no source, ABI, NoUB or production proof claim.
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const DRIVER: &str = r#"
#include <stdint.h>
#include <stddef.h>
extern uint64_t lean_uint64_add(uint64_t, uint64_t);
extern uint64_t lean_uint64_mul(uint64_t, uint64_t);
_Static_assert(_Generic(&lean_uint64_add,
  uint64_t (*)(uint64_t,uint64_t): 1, default: 0), "add ABI");
_Static_assert(_Generic(&lean_uint64_mul,
  uint64_t (*)(uint64_t,uint64_t): 1, default: 0), "mul ABI");
int main(void) {
  const uint64_t values[] = {0,1,2,3,UINT64_C(0x7fffffffffffffff),
    UINT64_C(0x8000000000000000),UINT64_C(0xfffffffffffffffe),UINT64_MAX};
  for (size_t a=0; a<sizeof(values)/sizeof(values[0]); ++a)
    for (size_t b=0; b<sizeof(values)/sizeof(values[0]); ++b) {
      if (lean_uint64_add(values[a], values[b]) != values[a]+values[b]) return 11;
      if (lean_uint64_mul(values[a], values[b]) != values[a]*values[b]) return 12;
    }
  return 0;
}
"#;

fn compile(dir: &Path, include: &Path, source: Option<&Path>, output: &Path) -> Output {
    let mut cc = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()));
    cc.args(["-std=c11", "-O0", "-Wall", "-Wextra", "-Werror", "-I"])
        .arg(include)
        .arg(dir.join("driver.c"));
    if let Some(source) = source {
        cc.arg(source);
    }
    cc.arg("-o")
        .arg(output)
        .output()
        .expect("C oracle compiler")
}

#[test]
fn test_actual_header_owners_materialize_scalar_symbols_with_mutation_controls() {
    let include = std::env::var_os("CLEAN_TEST_LEAN_INCLUDE")
        .map(PathBuf::from)
        .or_else(|| {
            clean_olean::pinned_lean_lib_path()
                .and_then(|lib| Some(lib.parent()?.parent()?.join("include")))
        })
        .expect("the actual repository-pinned Lean include directory is required");
    let header = include.join("lean/lean.h");
    let before = std::fs::read(&header).expect("actual Lean header input");
    let dir = tempfile::tempdir().expect("owned oracle directory");
    std::fs::write(dir.path().join("driver.c"), DRIVER).unwrap();

    // An ABI catalogue or header's internal linkage supplies no external owner.
    let absent = compile(dir.path(), &include, None, &dir.path().join("absent"));
    assert!(!absent.status.success(), "missing owners must not link");
    let stderr = String::from_utf8_lossy(&absent.stderr);
    assert!(
        stderr.contains("lean_uint64_add") && stderr.contains("lean_uint64_mul"),
        "{stderr}"
    );

    let source = dir.path().join("owner.c");
    let body = clean_runtime::lean_word64_extern_source();
    std::fs::write(&source, body).unwrap();
    let good = dir.path().join("good");
    let compiled = compile(dir.path(), &include, Some(&source), &good);
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    assert!(Command::new(good).status().unwrap().success());

    // Preserve compilation and linkage while changing the arithmetic result.
    for (operation, expected) in [("add", 11), ("mul", 12)] {
        let forward = format!("return lean_uint64_{operation}__clean_header_owner(left, right);");
        let changed = format!(
            "return lean_uint64_{operation}__clean_header_owner(left, right) ^ UINT64_C(1);"
        );
        let mutant = body.replace(&forward, &changed);
        assert_ne!(mutant, body);
        std::fs::write(&source, mutant).unwrap();
        let bad = dir.path().join(format!("changed-{operation}"));
        let compiled = compile(dir.path(), &include, Some(&source), &bad);
        assert!(
            compiled.status.success(),
            "{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        assert_eq!(Command::new(bad).status().unwrap().code(), Some(expected));
    }
    assert_eq!(std::fs::read(header).unwrap(), before);
}
