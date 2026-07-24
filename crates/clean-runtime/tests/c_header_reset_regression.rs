// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::ffi::OsString;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

struct CompiledHarness {
    work_dir: PathBuf,
    binary_path: PathBuf,
}

impl Drop for CompiledHarness {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.work_dir);
    }
}

fn compile_c_harness(source: &str) -> CompiledHarness {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after unix epoch")
        .as_nanos();
    let work_dir = std::env::temp_dir().join(format!(
        "clean-c-header-reset-{}-{unique}",
        std::process::id()
    ));
    fs::create_dir_all(&work_dir).expect("failed to create C harness temp dir");

    let source_path = work_dir.join("reset_regression.c");
    let binary_path = work_dir.join("reset_regression");
    fs::write(&source_path, source).expect("failed to write C harness source");

    let compiler = std::env::var_os("CC").unwrap_or_else(|| OsString::from("cc"));
    let output = Command::new(&compiler)
        .arg("-std=c11")
        .arg("-Wall")
        .arg("-Wextra")
        .arg("-Werror")
        .arg("-I")
        .arg(clean_runtime::include_dir())
        .arg(&source_path)
        .arg("-o")
        .arg(&binary_path)
        .output()
        .unwrap_or_else(|err| panic!("failed to launch C compiler {:?}: {err}", compiler));

    assert!(
        output.status.success(),
        "failed to compile C harness\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    CompiledHarness {
        work_dir,
        binary_path,
    }
}

#[test]
fn test_c_header_reset_decrements_nonreusable_hidden_children() {
    let harness = compile_c_harness(C_HEADER_RESET_REGRESSION);
    let output = Command::new(&harness.binary_path)
        .output()
        .expect("failed to run compiled C harness");

    assert!(
        output.status.success(),
        "C harness failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

const C_HEADER_RESET_REGRESSION: &str = r#"
#include "clean_runtime.h"

#include <stddef.h>
#include <stdio.h>

typedef struct test_leaf {
    clean_obj_header header;
} test_leaf;

typedef struct test_thunk {
    clean_obj_header header;
    clean_obj* value;
    clean_obj* closure;
} test_thunk;

typedef struct test_task {
    clean_obj_header header;
    clean_obj* value;
} test_task;

typedef struct test_external {
    clean_obj_header header;
    void* class_ptr;
    void* data;
    clean_obj* child;
} test_external;

typedef struct test_array {
    clean_obj_header header;
    size_t size;
    size_t capacity;
    clean_obj** data;
} test_array;

static int g_outer_dec_calls = 0;
static int g_child_dec_calls = 0;

static void init_header(clean_obj_header* header, uint8_t kind) {
    atomic_init(&header->ref_count, 0);
    header->tag = 0;
    header->kind = kind;
    header->num_objs = 0;
    header->scalar_sz = 0;
}

static test_leaf* alloc_leaf(void) {
    test_leaf* leaf = (test_leaf*)malloc(sizeof(test_leaf));
    init_header(&leaf->header, CLEAN_OBJ_KIND_CTOR);
    return leaf;
}

static test_thunk* alloc_test_thunk(void) {
    test_thunk* thunk = (test_thunk*)malloc(sizeof(test_thunk));
    init_header(&thunk->header, CLEAN_OBJ_KIND_THUNK);
    thunk->value = (clean_obj*)alloc_leaf();
    thunk->closure = (clean_obj*)alloc_leaf();
    return thunk;
}

static test_task* alloc_test_task(void) {
    test_task* task = (test_task*)malloc(sizeof(test_task));
    init_header(&task->header, CLEAN_OBJ_KIND_TASK);
    task->value = (clean_obj*)alloc_leaf();
    return task;
}

static test_external* alloc_test_external(void) {
    test_external* external = (test_external*)malloc(sizeof(test_external));
    init_header(&external->header, CLEAN_OBJ_KIND_EXTERNAL);
    external->class_ptr = NULL;
    external->data = NULL;
    external->child = (clean_obj*)alloc_leaf();
    return external;
}

static test_array* alloc_test_array(void) {
    test_array* array = (test_array*)malloc(sizeof(test_array));
    init_header(&array->header, CLEAN_OBJ_KIND_ARRAY);
    array->size = 1;
    array->capacity = 1;
    array->data = (clean_obj**)malloc(sizeof(clean_obj*));
    array->data[0] = (clean_obj*)alloc_leaf();
    return array;
}

static void reset_counters(void) {
    g_outer_dec_calls = 0;
    g_child_dec_calls = 0;
}

void clean_dec(clean_obj* o) {
    if (o == NULL || clean_is_scalar(o)) {
        return;
    }

    switch (o->header.kind) {
    case CLEAN_OBJ_KIND_THUNK: {
        test_thunk* thunk = (test_thunk*)o;
        g_outer_dec_calls += 1;
        clean_dec(thunk->value);
        clean_dec(thunk->closure);
        free(thunk);
        return;
    }
    case CLEAN_OBJ_KIND_TASK: {
        test_task* task = (test_task*)o;
        g_outer_dec_calls += 1;
        clean_dec(task->value);
        free(task);
        return;
    }
    case CLEAN_OBJ_KIND_EXTERNAL: {
        test_external* external = (test_external*)o;
        g_outer_dec_calls += 1;
        clean_dec(external->child);
        free(external);
        return;
    }
    case CLEAN_OBJ_KIND_ARRAY: {
        test_array* array = (test_array*)o;
        g_outer_dec_calls += 1;
        for (size_t i = 0; i < array->size; ++i) {
            clean_dec(array->data[i]);
        }
        free(array->data);
        free(array);
        return;
    }
    default:
        g_child_dec_calls += 1;
        free(o);
        return;
    }
}

static int expect_counts(const char* name, int expected_children) {
    if (g_outer_dec_calls != 1 || g_child_dec_calls != expected_children) {
        fprintf(
            stderr,
            "%s: expected outer=%d child=%d, got outer=%d child=%d\n",
            name,
            1,
            expected_children,
            g_outer_dec_calls,
            g_child_dec_calls
        );
        return 1;
    }
    return 0;
}

static int verify_thunk(void) {
    reset_counters();
    test_thunk* thunk = alloc_test_thunk();
    clean_obj* slot = clean_reset((clean_obj*)thunk);
    if (slot != NULL) {
        fprintf(stderr, "thunk: expected clean_reset to decline reuse\n");
        return 1;
    }
    return expect_counts("thunk", 2);
}

static int verify_task(void) {
    reset_counters();
    test_task* task = alloc_test_task();
    clean_obj* slot = clean_reset((clean_obj*)task);
    if (slot != NULL) {
        fprintf(stderr, "task: expected clean_reset to decline reuse\n");
        return 1;
    }
    return expect_counts("task", 1);
}

static int verify_external(void) {
    reset_counters();
    test_external* external = alloc_test_external();
    clean_obj* slot = clean_reset((clean_obj*)external);
    if (slot != NULL) {
        fprintf(stderr, "external: expected clean_reset to decline reuse\n");
        return 1;
    }
    return expect_counts("external", 1);
}

static int verify_array(void) {
    reset_counters();
    test_array* array = alloc_test_array();
    clean_obj* slot = clean_reset((clean_obj*)array);
    if (slot != NULL) {
        fprintf(stderr, "array: expected clean_reset to decline reuse\n");
        return 1;
    }
    return expect_counts("array", 1);
}

int main(void) {
    if (verify_thunk() != 0) {
        return 1;
    }
    if (verify_task() != 0) {
        return 2;
    }
    if (verify_external() != 0) {
        return 3;
    }
    if (verify_array() != 0) {
        return 4;
    }
    return 0;
}
"#;
