// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

static bool clean_driver_is_text(clean_obj* text) {
    return text && !clean_is_scalar(text) && text->header.kind == CLEAN_OBJ_KIND_STRING;
}

static bool clean_driver_error_ctor(clean_obj* value, unsigned tag, unsigned objects, size_t bytes) {
    return value && !clean_is_scalar(value) && value->header.kind == CLEAN_OBJ_KIND_CTOR &&
           value->header.tag == tag && value->header.num_objs == objects && value->header.scalar_sz == bytes;
}

static bool clean_driver_optional_text(clean_obj** value) {
    if (*value == clean_box(0)) {
        *value = NULL;
        return true;
    }
    if (!clean_driver_error_ctor(*value, 1, 1, 0)) return false;
    *value = clean_ctor_get(*value, 0);
    return clean_driver_is_text(*value);
}

/* The official runner prints the resulting string as a C string. An interior
 * NUL cuts off every later piece, including literals following this field. */
static void clean_driver_emit_bytes(bool* stopped, const char* s, size_t n, bool decapitalize) {
    if (*stopped || n == 0) return;
    const char* end = (const char*)memchr(s, 0, n);
    if (end) { n = (size_t)(end - s); *stopped = true; }
    if (n && decapitalize && s[0] >= 'A' && s[0] <= 'Z') {
        fputc(s[0] + ('a' - 'A'), stderr);
        ++s;
        --n;
    }
    if (n) fwrite(s, 1, n, stderr);
}

/* The checked UInt32 specialization fits every supported Lean target word. */
static void clean_driver_error_code(bool* stopped, uint32_t code) {
    _Static_assert(sizeof(size_t) >= sizeof(uint32_t), "the target word must hold a UInt32");
    if (*stopped) return;
    clean_obj* decimal = clean_usize_repr_owned(clean_box_uint64((uint64_t)(size_t)code));
    clean_driver_emit_bytes(stopped, clean_string_data(decimal), clean_string_len(decimal), false);
    clean_dec(decimal);
}
