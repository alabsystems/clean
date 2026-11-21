// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#include "clean_runtime.h"
#include <stdio.h>

/* Feed single independently mutated carriers to the actual source-bound driver. */
static clean_obj* test_result(unsigned tag, clean_obj* payload, clean_obj* world) {
#ifdef TEST_ERASED_WORLD
    clean_dec(world);
    return clean_alloc_ctor(tag, 1, 0, payload);
#else
    return clean_alloc_ctor(tag, 2, 0, payload, world);
#endif
}

static clean_obj* test_state_action(clean_obj* world) {
    const char* sample = getenv("CLEAN_TEST_NATIVE_RESULT");
    if (strcmp(sample, "status") == 0) return test_result(0, clean_box_uint32(23), world);
    if (strcmp(sample, "tag") == 0) return test_result(2, clean_box(23), world);
    if (strcmp(sample, "world") == 0) return clean_alloc_ctor(0, 2, 0, clean_box(23), clean_box(1));
    if (strcmp(sample, "arity") == 0) {
#ifdef TEST_ERASED_WORLD
        return clean_alloc_ctor(0, 2, 0, clean_box_uint32(23), world);
#else
        return clean_alloc_ctor(0, 1, 0, clean_box_uint32(23));
#endif
    }
    if (strcmp(sample, "payload") == 0) return test_result(0, clean_mk_string("23"), world);
    if (strcmp(sample, "scalar") == 0) return clean_box(23);
    if (strcmp(sample, "user_error") == 0) return test_result(1, clean_alloc_ctor(0, 1, 0, clean_mk_string("boom")), world);
    if (strcmp(sample, "error_tag") == 0) return test_result(1, clean_box(255), world);
    return NULL;
}

#ifdef TEST_RETURN_ACTION
static clean_obj* l_sourceEntry(void) {
    return clean_alloc_closure((void*)test_state_action, 1, 0);
}
#elif defined(TEST_ERASED_WORLD)
static clean_obj* l_sourceEntry(void) { return test_state_action(clean_box(0)); }
#else
static clean_obj* l_sourceEntry(clean_obj* world) { return test_state_action(world); }
#endif
