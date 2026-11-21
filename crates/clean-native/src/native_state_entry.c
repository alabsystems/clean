// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

/* Successful status reads borrow the payload; the driver consumes the owner. */
static int clean_driver_status(clean_obj* value, bool uint32, int* status) {
    if (!value) return 0;
    if (!uint32) {
        *status = 0;
        return value == clean_box(0);
    }
    if (clean_is_scalar(value)) {
        if (clean_unbox(value) > UINT32_MAX) return 0;
    } else if (value->header.kind != CLEAN_OBJ_KIND_CTOR ||
               value->header.tag != 0 || value->header.num_objs != 0 ||
               value->header.scalar_sz != sizeof(uint32_t)) {
        return 0;
    }
    *status = (int)clean_unbox_uint32(value);
    return 1;
}

static int clean_driver_finish_io(clean_obj* result, bool state, bool erased_world, bool uint32, unsigned user_error) {
    if (result && !clean_is_scalar(result) && result->header.kind == CLEAN_OBJ_KIND_CLOSURE && !state) {
        clean_closure* action = (clean_closure*)result;
        if (action->arity != action->num_fixed + 1) goto invalid;
        result = clean_apply_1(result, clean_box(0));
        state = true;
    }
    int status;
    if (!state && clean_driver_status(result, uint32, &status)) {
        clean_dec(result);
        return status;
    }
    if (!result || clean_is_scalar(result) || result->header.kind != CLEAN_OBJ_KIND_CTOR ||
        result->header.num_objs != (erased_world ? 1 : 2) || result->header.scalar_sz != 0 ||
        (!erased_world && clean_ctor_get(result, 1) != clean_box(0))) goto invalid;
    clean_obj* payload = clean_ctor_get(result, 0);
    if (result->header.tag == 0 && clean_driver_status(payload, uint32, &status)) {
        clean_dec(result);
        return status;
    }
#ifdef CLEAN_DRIVER_EXTENDED_IO_ERRORS
    if (result->header.tag == 1 && clean_driver_report_error(payload)) {
        clean_dec(result);
        return 1;
    }
#endif
    if (result->header.tag == 1 && payload && !clean_is_scalar(payload) &&
        payload->header.kind == CLEAN_OBJ_KIND_CTOR && payload->header.tag == user_error &&
        payload->header.num_objs == 1 && payload->header.scalar_sz == 0) {
        clean_obj* msg = clean_ctor_get(payload, 0);
        if (!msg || clean_is_scalar(msg) || msg->header.kind != CLEAN_OBJ_KIND_STRING) goto invalid;
        fputs("uncaught exception: ", stderr);
        /* Lean's uncaught-exception reporter prints a NUL-terminated string. */
        fputs(clean_string_data(msg), stderr);
        fputc('\n', stderr);
        clean_dec(result);
        return 1;
    }
invalid:
    if (result) clean_dec(result);
    fputs("clean: unsupported native IO result or error representation\n", stderr);
    return 1;
}
