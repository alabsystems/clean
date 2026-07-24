// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C-header regression tests for inline `clean_reset` behavior.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static C_HEADER_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

fn find_c_compiler() -> Option<&'static str> {
    ["cc", "gcc", "clang"].into_iter().find(|compiler| {
        Command::new(compiler)
            .arg("--version")
            .output()
            .map(|output| output.status.success())
            .unwrap_or(false)
    })
}

fn runtime_include_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("include")
}

fn compile_and_run_header_only_c(c_source: &str) -> Option<String> {
    let cc = match find_c_compiler() {
        Some(cc) => cc,
        None => {
            eprintln!("No C compiler found (cc/gcc/clang) — skipping C header regression");
            return None;
        }
    };

    let tmp_dir = std::env::temp_dir().join(format!(
        "clean_runtime_c_header_reset_{}_{}",
        std::process::id(),
        C_HEADER_TEST_COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&tmp_dir).expect("create temp dir");

    let source_path = tmp_dir.join("header_reset_test.c");
    let binary_path = tmp_dir.join("header_reset_test_bin");
    std::fs::write(&source_path, c_source).expect("write temp C source");

    let compile = Command::new(cc)
        .arg("-std=c11")
        .arg("-Wall")
        .arg("-Wextra")
        .arg("-Werror")
        .arg(format!("-I{}", runtime_include_dir().display()))
        .arg("-o")
        .arg(&binary_path)
        .arg(&source_path)
        .output()
        .expect("invoke C compiler");

    if !compile.status.success() {
        let stderr = String::from_utf8_lossy(&compile.stderr);
        let _ = std::fs::remove_dir_all(&tmp_dir);
        panic!(
            "C header compilation failed with {}:\n{}\n\nSource:\n{}",
            cc, stderr, c_source
        );
    }

    let run = Command::new(&binary_path)
        .output()
        .expect("execute compiled C regression");
    let _ = std::fs::remove_dir_all(&tmp_dir);

    if !run.status.success() {
        panic!(
            "Compiled C regression exited with {}:\nstdout: {}\nstderr: {}",
            run.status,
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr),
        );
    }

    Some(String::from_utf8_lossy(&run.stdout).trim().to_string())
}

const RESET_NON_REUSABLE_SOURCE: &str = r#"
#include "clean_runtime.h"
#include <stdint.h>
#include <stdio.h>

typedef struct {
    clean_obj_header header;
    clean_obj* value;
    clean_obj* closure;
} clean_thunk_local;

typedef struct {
    clean_obj_header header;
    clean_obj* value;
    void* imp;
} clean_task_local;

typedef struct {
    void (*finalize)(void*);
    void (*foreach)(void*, clean_obj*);
} clean_external_class_local;

typedef struct {
    clean_obj_header header;
    const clean_external_class_local* class_;
    void* data;
} clean_external_local;

typedef struct {
    clean_obj_header header;
    size_t size;
    size_t capacity;
    clean_obj* data[2];
} clean_array2_local;

static int leaf_decs = 0;
static int finalize_calls = 0;

static void init_header(clean_obj_header* header, uint8_t kind) {
    atomic_init(&header->ref_count, 0);
    header->tag = 0;
    header->kind = kind;
    header->num_objs = 0;
    header->scalar_sz = 0;
}

static clean_obj* make_leaf(void) {
    clean_obj* leaf = (clean_obj*)malloc(sizeof(clean_obj_header));
    init_header(&leaf->header, CLEAN_OBJ_KIND_CTOR);
    return leaf;
}

static void finalize_external(void* data) {
    finalize_calls += (int)(uintptr_t)data;
}

void clean_dec(clean_obj* o) {
    if (o == NULL || clean_is_scalar(o)) {
        return;
    }

    switch (o->header.kind) {
    case CLEAN_OBJ_KIND_ARRAY: {
        clean_array2_local* arr = (clean_array2_local*)o;
        for (size_t i = 0; i < arr->size; i++) {
            clean_dec(arr->data[i]);
        }
        return;
    }
    case CLEAN_OBJ_KIND_THUNK: {
        clean_thunk_local* thunk = (clean_thunk_local*)o;
        clean_dec(thunk->value);
        clean_dec(thunk->closure);
        return;
    }
    case CLEAN_OBJ_KIND_TASK: {
        clean_task_local* task = (clean_task_local*)o;
        clean_dec(task->value);
        return;
    }
    case CLEAN_OBJ_KIND_EXTERNAL: {
        clean_external_local* ext = (clean_external_local*)o;
        if (ext->class_ != NULL && ext->class_->finalize != NULL) {
            ext->class_->finalize(ext->data);
        }
        return;
    }
    default:
        leaf_decs += 1;
        return;
    }
}

int main(void) {
    int baseline = 0;

    clean_thunk_local thunk;
    init_header(&thunk.header, CLEAN_OBJ_KIND_THUNK);
    thunk.value = make_leaf();
    thunk.closure = make_leaf();
    baseline = leaf_decs;
    if (clean_reset((clean_obj*)&thunk) != NULL || leaf_decs != baseline + 2) {
        fprintf(stderr, "thunk reset should dec value+closure and return NULL\n");
        return 1;
    }

    clean_task_local task;
    init_header(&task.header, CLEAN_OBJ_KIND_TASK);
    task.value = make_leaf();
    task.imp = NULL;
    baseline = leaf_decs;
    if (clean_reset((clean_obj*)&task) != NULL || leaf_decs != baseline + 1) {
        fprintf(stderr, "task reset should dec value and return NULL\n");
        return 1;
    }

    clean_external_class_local external_class = {
        .finalize = finalize_external,
        .foreach = NULL,
    };
    clean_external_local external;
    init_header(&external.header, CLEAN_OBJ_KIND_EXTERNAL);
    external.class_ = &external_class;
    external.data = (void*)(uintptr_t)1;
    if (clean_reset((clean_obj*)&external) != NULL || finalize_calls != 1) {
        fprintf(stderr, "external reset should finalize and return NULL\n");
        return 1;
    }

    clean_array2_local array;
    init_header(&array.header, CLEAN_OBJ_KIND_ARRAY);
    array.size = 2;
    array.capacity = 2;
    array.data[0] = make_leaf();
    array.data[1] = make_leaf();
    baseline = leaf_decs;
    if (clean_reset((clean_obj*)&array) != NULL || leaf_decs != baseline + 2) {
        fprintf(stderr, "array reset should dec elements and return NULL\n");
        return 1;
    }

    printf("ok\n");
    return 0;
}
"#;

#[test]
fn test_c_header_reset_non_reusable_kinds_delegate_whole_object_teardown() {
    if let Some(output) = compile_and_run_header_only_c(RESET_NON_REUSABLE_SOURCE) {
        assert_eq!(
            output, "ok",
            "clean_reset must route non-reusable C-header kinds through whole-object teardown",
        );
    }
}
