/*
 * Copyright 2026 Andrew Yates
 * SPDX-License-Identifier: Apache-2.0
 */

#include "clean_runtime.h"
#include <stdio.h>

static clean_obj* keep(clean_obj* object) {
    clean_inc(object);
    return object;
}

static void out(const char* label, clean_obj* n) {
    clean_obj* text = clean_nat_repr(n);
    printf("%s=%s\n", label, clean_string_data(text));
    clean_dec(text);
}

static void flag(const char* label, clean_obj* boolean) {
    printf("%s=%s\n", label, clean_unbox(boolean) ? "true" : "false");
}

static void word(const char* label, clean_obj* n, uint64_t mask) {
    uint64_t low = clean_nat_low_u64(n);
    assert(clean_unbox_uint64(n) == low);
    assert(clean_unbox_uint32(n) == (uint32_t)low);
    clean_dec(n);
    out(label, clean_nat_of_u64(low & mask));
}

static clean_obj* bit(clean_obj* n, clean_obj* index) {
    return clean_nat_land(clean_nat_shift_right(n, index), clean_box(1));
}

static void check_copy(void) {
    uint64_t words[] = {0x6421, 0, 7, 0};
    clean_obj* first = clean_nat_from_limbs(words, 4);
    unsigned char bytes[33] = {0};
    bytes[1] = 0x21;
    bytes[2] = 0x64;
    bytes[17] = 7;
    clean_obj* second = clean_nat_from_le_bytes(bytes + 1, 32);
    words[0] = 0;
    bytes[1] = 0;
    assert(clean_unbox(clean_nat_dec_eq(keep(first), second)) == 1);

    assert(clean_is_exclusive(first));
    assert(clean_reset(first) == NULL);
    assert(clean_nat_from_limbs(NULL, 0) == clean_box(0));
    assert(clean_nat_from_le_bytes(NULL, 0) == clean_box(0));
    assert(clean_nat_to_u128(clean_box(42)) == 42);
    clean_obj* legacy = clean_box_uint64(UINT64_MAX);
    assert(clean_nat_to_u128(legacy) == UINT64_MAX);
    clean_dec(legacy);
}

static void vectors(void) {
    clean_obj* a = clean_nat_from_limbs((uint64_t[]){17, 1, 1, 1}, 4);
    clean_obj* b = clean_nat_from_limbs((uint64_t[]){32, 1, 2}, 3);
    clean_obj* c = clean_nat_big(3, 2);
    out("a", keep(a));
    out("b", keep(b));
    out("max128+1", clean_nat_add(clean_nat_big(UINT64_MAX, UINT64_MAX), clean_box(1)));
    out("add", clean_nat_add(keep(a), keep(b)));
    out("add_self", clean_nat_add(keep(a), keep(a)));
    out("sub", clean_nat_sub(keep(a), keep(b)));
    out("sub_sat", clean_nat_sub(keep(b), keep(a)));
    out("mul", clean_nat_mul(keep(a), keep(b)));
    out("mul_0", clean_nat_mul(keep(a), clean_box(0)));
    out("pow_zero_zero", clean_nat_pow(clean_box(0), clean_box(0)));
    out("pow_wide_zero", clean_nat_pow(keep(a), clean_box(0)));
    out("pow_wide_one", clean_nat_pow(keep(a), clean_box(1)));
    out("pow_wide_three", clean_nat_pow(keep(a), clean_box(3)));
    out("pow_cross_limb", clean_nat_pow(clean_box(2), clean_box(65)));
    out("pow_zero_oversized", clean_nat_pow(clean_box(0), keep(b)));
    out("pow_one_oversized", clean_nat_pow(clean_box(1), keep(b)));
    out("pow_one_at_limit", clean_nat_pow(clean_box(1), clean_nat_of_u64(UINT32_MAX)));
    clean_obj* scalar_power = clean_nat_pow(clean_box(2), clean_box(4194305));
    flag("pow_large_scalar", clean_nat_beq(scalar_power,
        clean_nat_shift_left(clean_box(1), clean_box(4194305))));
    clean_obj* heap_base = clean_nat_from_limbs((uint64_t[]){0, 0, 4}, 3);
    clean_obj* heap_power = clean_nat_pow(keep(heap_base), clean_box(32265));
    flag("pow_large_heap", clean_nat_beq(heap_power,
        clean_nat_shift_left(clean_box(1), clean_box(4194450))));
    assert(clean_is_exclusive(heap_base));
    clean_dec(heap_base);
    out("div_wide", clean_nat_div(keep(a), keep(b)));
    out("mod_wide", clean_nat_mod(keep(a), keep(b)));
    out("div_mid", clean_nat_div(keep(a), keep(c)));
    out("mod_mid", clean_nat_mod(keep(a), c));
    out("div_word", clean_nat_div(keep(a), clean_box(3)));
    out("mod_word", clean_nat_mod(keep(a), clean_box(3)));
    out("div_zero", clean_nat_div(keep(a), clean_box(0)));
    out("mod_zero", clean_nat_mod(keep(a), clean_box(0)));
    out("div_larger", clean_nat_div(keep(b), keep(a)));
    out("mod_larger", clean_nat_mod(keep(b), keep(a)));
    out("div_equal", clean_nat_div(keep(a), keep(a)));
    out("mod_equal", clean_nat_mod(keep(a), keep(a)));
    out("and", clean_nat_land(keep(a), keep(b)));
    out("or", clean_nat_lor(keep(a), keep(b)));
    out("xor", clean_nat_xor(keep(a), keep(b)));
    out("xor_self", clean_nat_xor(keep(a), keep(a)));
    out("right_63", clean_nat_shift_right(keep(a), clean_box(63)));
    out("right_64", clean_nat_shift_right(keep(a), clean_box(64)));
    out("right_65", clean_nat_shift_right(keep(a), clean_box(65)));
    out("right_128", clean_nat_shift_right(keep(a), clean_box(128)));
    out("right_192", clean_nat_shift_right(keep(a), clean_box(192)));
    out("right_193", clean_nat_shift_right(keep(a), clean_box(193)));
    out("right_huge", clean_nat_shift_right(keep(a), keep(b)));
    out("left_63", clean_nat_shift_left(keep(a), clean_box(63)));
    out("left_64", clean_nat_shift_left(keep(a), clean_box(64)));
    out("left_65", clean_nat_shift_left(keep(a), clean_box(65)));
    out("left_129", clean_nat_shift_left(keep(a), clean_box(129)));
    flag("eq_wide", clean_nat_beq(keep(a), keep(a)));
    flag("ne_wide", clean_nat_beq(keep(a), keep(b)));
    flag("le_wide", clean_nat_ble(keep(b), keep(a)));
    flag("gt_wide", clean_nat_blt(keep(a), keep(b)));
    flag("test_bit_192", bit(keep(a), clean_box(192)));
    flag("test_bit_huge", bit(keep(a), keep(b)));
    word("uint8", clean_nat_add(keep(a), clean_box(0x1234)), UINT8_MAX);
    word("uint16", clean_nat_add(keep(a), clean_box(0x12345)), UINT16_MAX);
    word("uint32", clean_nat_add(keep(a), clean_box(UINT64_C(0x123456789))), UINT32_MAX);
    word("uint64", clean_nat_add(keep(a), clean_nat_big(UINT64_C(0x23456789abcdef01), 1)), UINT64_MAX);
    word("usize", clean_nat_add(keep(a), clean_nat_big(UINT64_C(0x23456789abcdef01), 1)), SIZE_MAX);

    clean_obj* pos_a = clean_alloc_ctor(0, 1, 0, keep(a));
    clean_obj* pos_b = clean_alloc_ctor(0, 1, 0, keep(b));
    flag("int_signed_pos_cmp", clean_int_dec_lt(pos_b, pos_a));
    clean_obj* neg_a = clean_alloc_ctor(1, 1, 0, keep(a));
    clean_obj* neg_b = clean_alloc_ctor(1, 1, 0, keep(b));
    flag("int_signed_neg_cmp", clean_int_dec_lt(keep(neg_a), neg_b));
    flag("int_signed_neg_eq", clean_int_dec_eq(keep(neg_a), neg_a));
    assert(clean_is_exclusive(a) && clean_is_exclusive(b));
    clean_dec(a);
    clean_dec(b);
}

static void boundary(void) {
    clean_obj* n = clean_nat_shift_left(clean_box(1), clean_box(2048));
    clean_obj* half = clean_nat_shift_left(clean_box(1), clean_box(1024));
    clean_obj* previous = clean_nat_sub(keep(n), clean_box(1));
    clean_obj* plus = clean_nat_add(keep(n), clean_box(17));
    out("2048_bit", keep(n));
    out("2048_to_0", clean_nat_shift_right(keep(n), clean_box(2048)));
    out("2048_to_1", clean_nat_shift_right(keep(n), clean_box(2047)));
    out("2048_to_negative", clean_nat_shift_right(keep(n), clean_box(2049)));
    out("carry_32_limbs", clean_nat_add(keep(previous), clean_box(1)));
    out("borrow_32_limbs", keep(previous));
    out("mul_cross_32", clean_nat_mul(keep(half), keep(half)));
    out("div_cross_32", clean_nat_div(keep(plus), keep(half)));
    out("mod_cross_32", clean_nat_mod(keep(plus), half));
    out("and_mask_32", clean_nat_land(plus, previous));
    out("alias_32", clean_nat_add(keep(n), n));
}

int main(int argc, char** argv) {
    if (argc > 1) {
        if (strcmp(argv[1], "narrow") == 0) {
            clean_obj* wide = clean_nat_from_limbs((uint64_t[]){0, 0, 1}, 3);
            (void)clean_nat_to_u128(wide);
            clean_dec(wide);
        } else if (strcmp(argv[1], "char-wide") == 0) {
            clean_obj* wide = clean_nat_from_limbs((uint64_t[]){65, 0, 1}, 3);
            (void)clean_char_from_valid_nat_owned(wide, clean_box(0));
        } else if (strcmp(argv[1], "char-surrogate") == 0) {
            (void)clean_char_from_valid_nat_owned(clean_box(0xd800), clean_box(0));
        } else if (strcmp(argv[1], "char-proof") == 0) {
            (void)clean_char_from_valid_nat_owned(clean_box(65), clean_box(1));
        } else if (strcmp(argv[1], "pow-exponent-cutoff") == 0) {
            (void)clean_nat_pow(clean_box(2), clean_nat_of_u64(UINT64_C(0x100000000)));
        } else if (strcmp(argv[1], "pow-aliased-oversized") == 0) {
            clean_obj* wide = clean_nat_from_limbs((uint64_t[]){5, 0, 1}, 3);
            (void)clean_nat_pow(keep(wide), wide);
        } else {
            (void)clean_nat_from_le_bytes(NULL, 7);
        }
        return 99;
    }
    clean_obj* shared = clean_box_uint64(0x10ffff);
    clean_obj* scalar = clean_char_from_valid_nat_owned(keep(shared), clean_box(0));
    assert(clean_unbox_uint32(scalar) == 0x10ffff);
    assert(clean_is_exclusive(shared));
    clean_dec(scalar);
    clean_dec(shared);
    check_copy();
    vectors();
    boundary();
    return 0;
}
