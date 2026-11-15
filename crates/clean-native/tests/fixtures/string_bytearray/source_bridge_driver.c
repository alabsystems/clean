#include "clean_runtime.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

#ifdef CLEAN_BRIDGE_CG
#ifdef __APPLE__
#define BRIDGE_LABEL(name) __asm__("_" name)
#else
#define BRIDGE_LABEL(name) __asm__(name)
#endif
extern clean_obj* bridge_dynamic(clean_obj*) BRIDGE_LABEL("bridgeDynamic");
extern clean_obj* bridge_partial(clean_obj*) BRIDGE_LABEL("bridgeDynamicPartial");
extern clean_obj* bridge_selected(clean_obj*) BRIDGE_LABEL("bridgeDynamicSelected");
extern clean_obj* bridge_payload(clean_obj*) BRIDGE_LABEL("bridgePayload");
extern clean_obj* bridge_cases(clean_obj*) BRIDGE_LABEL("bridgePayloadCases");
extern clean_obj* bridge_roundtrip(clean_obj*) BRIDGE_LABEL("bridgeRoundTrip");
extern clean_obj* bridge_rewrap(clean_obj*) BRIDGE_LABEL("bridgeRewrap");
extern clean_obj* bridge_shared(clean_obj*) BRIDGE_LABEL("bridgeShared");
extern clean_obj* bridge_chars(clean_obj*) BRIDGE_LABEL("bridgeFromChars");
extern clean_obj* bridge_entry(void) BRIDGE_LABEL("bridgeEntry");
#else
#define bridge_dynamic l_bridgeDynamic
#define bridge_partial l_bridgeDynamicPartial
#define bridge_selected l_bridgeDynamicSelected
#define bridge_payload l_bridgePayload
#define bridge_cases l_bridgePayloadCases
#define bridge_roundtrip l_bridgeRoundTrip
#define bridge_rewrap l_bridgeRewrap
#define bridge_shared l_bridgeShared
#define bridge_chars l_bridgeFromChars
#define bridge_entry l_bridgeEntry
#endif

static void check_string(clean_obj* value, const unsigned char* expected, size_t len) {
    assert(value != NULL && !clean_is_scalar(value));
    assert(value->header.kind == CLEAN_OBJ_KIND_STRING);
    assert(clean_string_len(value) == len);
    assert(memcmp(clean_string_data(value), expected, len) == 0);
    fwrite(clean_string_data(value), 1, len, stdout);
    fputc('\n', stdout);
}

static void check_bytes(clean_obj* list, const unsigned char* expected, size_t len) {
    clean_obj* p = list;
    for (size_t i = 0; i < len; i++) {
        assert(p != NULL && !clean_is_scalar(p));
        assert(p->header.kind == CLEAN_OBJ_KIND_CTOR && p->header.tag == 1);
        assert(p->header.num_objs == 2);
        clean_obj* byte = clean_ctor_get(p, 0);
        assert(clean_is_scalar(byte) && clean_unbox(byte) == expected[i]);
        p = clean_ctor_get(p, 1);
    }
    assert(p == clean_box(0));
}

int main(int argc, char** argv) {
    (void)argv;
    uint32_t n = (uint32_t)(argc - 1);
    unsigned char expected[] = {97 + (unsigned char)n, 0, 0xce, 0xbb, 0xf0, 0x9f, 0x98, 0x80};
    clean_obj* value = bridge_dynamic(clean_nat_of_u64(n));
    check_string(value, expected, sizeof(expected));
    clean_obj* partial = bridge_partial(clean_nat_of_u64(n));
    check_string(partial, expected, sizeof(expected));
    clean_dec(partial);
    clean_obj* selected = bridge_selected(clean_nat_of_u64(n));
    check_string(selected, expected, sizeof(expected));
    clean_dec(selected);
    clean_inc(value);
    clean_obj* direct = bridge_payload(value);
    check_bytes(direct, expected, sizeof(expected));
    clean_dec(direct);
    clean_inc(value);
    clean_obj* cases = bridge_cases(value);
    check_bytes(cases, expected, sizeof(expected));
    clean_dec(cases);
    clean_inc(value);
    clean_obj* roundtrip = bridge_roundtrip(value);
    check_string(roundtrip, expected, sizeof(expected));
    clean_dec(roundtrip);
    clean_inc(value);
    clean_obj* rewrapped = bridge_rewrap(value);
    check_string(rewrapped, expected, sizeof(expected));
    clean_dec(rewrapped);
    uint32_t cps[] = {0, 233, 8364, 128512 + n};
    clean_obj* chars = clean_box(0);
    for (size_t i = 4; i > 0; i--) {
        chars = clean_alloc_ctor(1, 2, 0, clean_box_uint32(cps[i - 1]), chars);
    }
    unsigned char encoded_chars[] = {0, 0xc3, 0xa9, 0xe2, 0x82, 0xac, 0xf0, 0x9f, 0x98, 0x80 + (unsigned char)n};
    clean_obj* from_chars = bridge_chars(chars);
    check_string(from_chars, encoded_chars, sizeof(encoded_chars));
    clean_dec(from_chars);
    clean_inc(value);
    clean_obj* pair = bridge_shared(value);
    assert(pair != NULL && !clean_is_scalar(pair));
    assert(pair->header.kind == CLEAN_OBJ_KIND_CTOR && pair->header.num_objs == 2);
    check_string(clean_ctor_get(pair, 0), expected, sizeof(expected));
    check_string(clean_ctor_get(pair, 1), expected, sizeof(expected));
    clean_dec(pair);
    assert(atomic_load(&value->header.ref_count) == 0);
    clean_dec(value);
    clean_obj* empty = clean_mk_string_from_bytes(NULL, 0);
    clean_obj* empty_roundtrip = bridge_roundtrip(empty);
    check_string(empty_roundtrip, (const unsigned char*)"", 0);
    clean_dec(empty_roundtrip);
    assert(clean_nat_to_u128(bridge_entry()) == 3);
    return 0;
}
