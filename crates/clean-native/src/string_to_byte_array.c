clean_obj* l_String_toByteArray(clean_obj* string) {
/* Copyright 2026 Andrew Yates
 * SPDX-License-Identifier: Apache-2.0 */

/* Return fresh owned constructor wrappers and boxed UInt8 list elements.
 * Consume the input reference only after its entire byte payload is copied. */

    if (string == NULL || clean_is_scalar(string) ||
        string->header.kind != CLEAN_OBJ_KIND_STRING) {
        clean_panic("String.toByteArray: expected flat String");
    }
    const unsigned char* data = (const unsigned char*)clean_string_data(string);
    size_t len = clean_string_len(string);
    clean_obj* list = clean_box(0);
    for (size_t i = len; i > 0; i--) {
        list = clean_alloc_ctor(1, 2, 0, clean_box(data[i - 1]), list);
    }
    clean_obj* array = clean_alloc_ctor(0, 1, 0, list);
    clean_obj* bytes = clean_alloc_ctor(0, 1, 0, array);
    clean_dec(string);
    return bytes;
}
