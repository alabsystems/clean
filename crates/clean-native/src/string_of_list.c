clean_obj* l_String_ofList(clean_obj* chars) {
    /* Copyright 2026 Andrew Yates
     * SPDX-License-Identifier: Apache-2.0
     * The genuine String.ofList runtime primitive encodes valid Char scalars.
     * This is not a List-Char String constructor. Consume the owned input
     * list only after the complete UTF-8 payload has been copied. */
    clean_obj* p = chars;
    size_t len = 0;
    while (!clean_is_scalar(p)) {
        if (p == NULL || p->header.kind != CLEAN_OBJ_KIND_CTOR ||
            p->header.tag != 1 || p->header.num_objs != 2 ||
            p->header.scalar_sz != 0) {
            clean_panic("String.ofList: expected List Char constructor");
        }
        clean_obj* c = clean_ctor_get(p, 0);
        if (c == NULL || (!clean_is_scalar(c) &&
            (c->header.kind != CLEAN_OBJ_KIND_CTOR || c->header.num_objs != 0 ||
             c->header.scalar_sz != sizeof(uint32_t)))) {
            clean_panic("String.ofList: expected boxed Char scalar");
        }
        uint64_t raw = clean_is_scalar(c) ? clean_unbox(c) : clean_unbox_uint32(c);
        if (raw > 0x10ffff || (raw >= 0xd800 && raw <= 0xdfff)) {
            clean_panic("String.ofList: invalid Unicode scalar");
        }
        uint32_t cp = (uint32_t)raw;
        size_t width = cp < 0x80 ? 1 : (cp < 0x800 ? 2 : (cp < 0x10000 ? 3 : 4));
        if (len > SIZE_MAX - width) {
            clean_panic("String.ofList: byte count overflow");
        }
        len += width;
        p = clean_ctor_get(p, 1);
    }
    if (p != clean_box(0)) {
        clean_panic("String.ofList: expected List.nil");
    }
    char* data = len == 0 ? NULL : (char*)malloc(len);
    if (len != 0 && data == NULL) {
        clean_panic("String.ofList: allocation failed");
    }
    size_t k = 0;
    p = chars;
    while (!clean_is_scalar(p)) {
        uint32_t cp = clean_unbox_uint32(clean_ctor_get(p, 0));
        if (cp < 0x80) {
            data[k++] = (char)cp;
        } else if (cp < 0x800) {
            data[k++] = (char)(0xc0 | (cp >> 6));
            data[k++] = (char)(0x80 | (cp & 0x3f));
        } else if (cp < 0x10000) {
            data[k++] = (char)(0xe0 | (cp >> 12));
            data[k++] = (char)(0x80 | ((cp >> 6) & 0x3f));
            data[k++] = (char)(0x80 | (cp & 0x3f));
        } else {
            data[k++] = (char)(0xf0 | (cp >> 18));
            data[k++] = (char)(0x80 | ((cp >> 12) & 0x3f));
            data[k++] = (char)(0x80 | ((cp >> 6) & 0x3f));
            data[k++] = (char)(0x80 | (cp & 0x3f));
        }
        p = clean_ctor_get(p, 1);
    }
    clean_obj* result = clean_mk_string_from_bytes(data, len);
    free(data);
    clean_dec(chars);
    return result;
}
