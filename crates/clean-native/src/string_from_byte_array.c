clean_obj* l_String_ofByteArray(clean_obj* bytes, clean_obj* proof) {
/* Copyright 2026 Andrew Yates
 * SPDX-License-Identifier: Apache-2.0 */

/* Clean's native Array/ByteArray use ordinary constructor cells around a
 * boxed List UInt8. The checked String proof is erased. Consume the payload
 * reference transferred by the generated call, after copying all bytes. */

    (void)proof;
    if (bytes == NULL || clean_is_scalar(bytes) ||
        bytes->header.kind != CLEAN_OBJ_KIND_CTOR || bytes->header.tag != 0 ||
        bytes->header.num_objs != 1 || bytes->header.scalar_sz != 0) {
        clean_panic("String.ofByteArray: expected ByteArray constructor");
    }
    clean_obj* array = clean_ctor_get(bytes, 0);
    if (array == NULL || clean_is_scalar(array) ||
        array->header.kind != CLEAN_OBJ_KIND_CTOR || array->header.tag != 0 ||
        array->header.num_objs != 1 || array->header.scalar_sz != 0) {
        clean_panic("String.ofByteArray: expected Array constructor");
    }
    clean_obj* list = clean_ctor_get(array, 0);
    clean_obj* p = list;
    size_t len = 0;
    while (!clean_is_scalar(p)) {
        if (p == NULL || p->header.kind != CLEAN_OBJ_KIND_CTOR ||
            p->header.tag != 1 || p->header.num_objs != 2 ||
            p->header.scalar_sz != 0) {
            clean_panic("String.ofByteArray: expected List UInt8 constructor");
        }
        clean_obj* byte = clean_ctor_get(p, 0);
        if (!clean_is_scalar(byte) || clean_unbox(byte) > UINT8_MAX) {
            clean_panic("String.ofByteArray: expected boxed UInt8");
        }
        if (len == SIZE_MAX) {
            clean_panic("String.ofByteArray: byte count overflow");
        }
        len++;
        p = clean_ctor_get(p, 1);
    }
    if (p != clean_box(0)) {
        clean_panic("String.ofByteArray: expected List.nil");
    }
    char* data = len == 0 ? NULL : (char*)malloc(len);
    if (len != 0 && data == NULL) {
        clean_panic("String.ofByteArray: allocation failed");
    }
    p = list;
    for (size_t i = 0; i < len; i++) {
        data[i] = (char)clean_unbox(clean_ctor_get(p, 0));
        p = clean_ctor_get(p, 1);
    }
    clean_obj* result = clean_mk_string_from_bytes(data, len);
    free(data);
    clean_dec(bytes);
    return result;
}
