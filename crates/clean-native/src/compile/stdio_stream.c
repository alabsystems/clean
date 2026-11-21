/* Copyright 2026 Andrew Yates
 * SPDX-License-Identifier: Apache-2.0
 *
 * The source selector checks the stable boxed ST/EST and Stream layouts.
 * Methods here consume exactly the arguments of that boxed calling convention.
 * The operating system handle remains owned by the process.
 */

#include <pthread.h>
#include <unistd.h>

static void* clean_stdio_malloc(size_t n) {
    void* result = malloc(n);
    if (!result) clean_panic("IO.FS.Handle: allocation failed");
    return result;
}

static clean_obj* clean_stdio_result(unsigned tag, clean_obj* value, clean_obj* world) {
#ifdef CLEAN_STDIO_ERASED_WORLD
    clean_dec(world);
    return clean_alloc_ctor(tag, 1, 0, value);
#else
    return clean_alloc_ctor(tag, 2, 0, value, world);
#endif
}

static clean_obj* clean_stdio_ok(clean_obj* value, clean_obj* world) {
    return clean_stdio_result(0, value, world);
}

static clean_obj* clean_stdio_error(int code, clean_obj* world) {
    return clean_stdio_result(1, clean_stdio_errno_payload(code), world);
}

static clean_obj* clean_stdio_handle_put_str(FILE* file, clean_obj* text, clean_obj* world) {
    if (!text || clean_is_scalar(text) || text->header.kind != CLEAN_OBJ_KIND_STRING)
        clean_panic("IO.FS.Handle.putStr: expected checked String");
    size_t len = clean_string_len(text);
    size_t written = fwrite(clean_string_data(text), 1, len, file);
    int error = errno;
    clean_dec(text);
    return written == len ? clean_stdio_ok(clean_box(0), world) : clean_stdio_error(error, world);
}

static clean_obj* clean_stdout_put_str(clean_obj* text, clean_obj* world) {
    return clean_stdio_handle_put_str(stdout, text, world);
}

static clean_obj* clean_stdout_flush(clean_obj* world) {
    return fflush(stdout) == 0 ? clean_stdio_ok(clean_box(0), world) : clean_stdio_error(errno, world);
}

static clean_obj* clean_stdout_is_tty(clean_obj* world) {
    return clean_stdio_ok(clean_box(isatty(fileno(stdout)) != 0), world);
}

static bool clean_stdio_ctor(clean_obj* object, unsigned tag, unsigned fields) {
    return object && !clean_is_scalar(object) && object->header.kind == CLEAN_OBJ_KIND_CTOR
        && object->header.tag == tag && object->header.num_objs == fields && !object->header.scalar_sz;
}

static clean_obj* clean_stdio_byte_array(const unsigned char* bytes, size_t length) {
    clean_obj* list = clean_box(0);
    while (length) {
        list = clean_alloc_ctor(1, 2, 0, clean_box(bytes[--length]), list);
    }
    return clean_alloc_ctor(0, 1, 0, clean_alloc_ctor(0, 1, 0, list));
}

static clean_obj* clean_stdout_read(clean_obj* count, clean_obj* world) {
    size_t n = (size_t)clean_unbox_uint64(count);
    clean_dec(count);
    /* Header, size, and capacity of the source SDK's unboxed byte array. */
    if (n > SIZE_MAX - 3 * sizeof(void*)) return clean_stdio_error(ENOMEM, world);
    if (!n) return clean_stdio_ok(clean_stdio_byte_array(NULL, 0), world);
    unsigned char* buffer = clean_stdio_malloc(n);
    size_t got = fread(buffer, 1, n, stdout);
    int error = errno;
    clean_obj* result;
    if (got) {
        result = clean_stdio_ok(clean_stdio_byte_array(buffer, got), world);
    } else if (feof(stdout)) {
        clearerr(stdout);
        result = clean_stdio_ok(clean_stdio_byte_array(NULL, 0), world);
    } else {
        result = clean_stdio_error(error, world);
    }
    free(buffer);
    return result;
}

static clean_obj* clean_stdout_write(clean_obj* value, clean_obj* world) {
    if (!clean_stdio_ctor(value, 0, 1) || !clean_stdio_ctor(clean_ctor_get(value, 0), 0, 1))
        clean_panic("IO.FS.Handle.write: expected checked ByteArray");
    clean_obj* list = clean_ctor_get(clean_ctor_get(value, 0), 0);
    size_t n = 0;
    for (clean_obj* tail = list; tail != clean_box(0); tail = clean_ctor_get(tail, 1)) {
        if (!clean_stdio_ctor(tail, 1, 2)) clean_panic("IO.FS.Handle.write: expected List UInt8");
        clean_obj* byte = clean_ctor_get(tail, 0);
        if (!clean_is_scalar(byte) || clean_unbox(byte) > UINT8_MAX)
            clean_panic("IO.FS.Handle.write: expected UInt8");
        if (n == SIZE_MAX) clean_panic("IO.FS.Handle.write: byte count overflow");
        ++n;
    }
    unsigned char* bytes = n ? clean_stdio_malloc(n) : NULL;
    for (size_t i = 0; i < n; ++i, list = clean_ctor_get(list, 1))
        bytes[i] = (unsigned char)clean_unbox(clean_ctor_get(list, 0));
    size_t written = n ? fwrite(bytes, 1, n, stdout) : 0;
    int error = errno;
    free(bytes);
    clean_dec(value);
    return written == n ? clean_stdio_ok(clean_box(0), world) : clean_stdio_error(error, world);
}

/* A malformed lead and its following consecutive continuation bytes become
 * one replacement character in Lean's checked String constructor. */
static size_t clean_stdio_utf8_width(const unsigned char* bytes, size_t n) {
    unsigned c = bytes[0];
    if (c < 0x80) return 1;
    size_t width = c >= 0xc2 && c <= 0xdf ? 2 :
                   c >= 0xe0 && c <= 0xef ? 3 :
                   c >= 0xf0 && c <= 0xf4 ? 4 : 0;
    if (!width || n < width) return 0;
    for (size_t i = 1; i < width; ++i)
        if ((bytes[i] & 0xc0) != 0x80) return 0;
    if ((c == 0xe0 && bytes[1] < 0xa0) || (c == 0xed && bytes[1] >= 0xa0) ||
        (c == 0xf0 && bytes[1] < 0x90) || (c == 0xf4 && bytes[1] >= 0x90)) return 0;
    return width;
}

static size_t clean_stdio_recover_text(const unsigned char* bytes, size_t length, char* output,
                                      bool* repaired) {
    size_t size = 0;
    for (size_t i = 0; i < length;) {
        size_t width = clean_stdio_utf8_width(bytes + i, length - i);
        size_t add = width ? width : 3;
        if (size > SIZE_MAX - add) clean_panic("IO.FS.Handle.getLine: string size overflow");
        if (width) {
            if (output) memcpy(output + size, bytes + i, width);
            i += width;
        } else {
            *repaired = true;
            if (output) memcpy(output + size, "\xef\xbf\xbd", 3);
            do { ++i; } while (i < length && (bytes[i] & 0xc0) == 0x80);
        }
        size += add;
    }
    return size;
}

static clean_obj* clean_stdio_line_text(const char* line, size_t length) {
    bool repaired = false;
    const unsigned char* bytes = (const unsigned char*)line;
    size_t size = clean_stdio_recover_text(bytes, length, NULL, &repaired);
    if (!repaired) return clean_mk_string_from_bytes(line, length);
    char* buffer = clean_stdio_malloc(size);
    clean_stdio_recover_text(bytes, length, buffer, &repaired);
    clean_obj* text = clean_mk_string_from_bytes(buffer, size);
    free(buffer);
    return text;
}

static clean_obj* clean_stdout_get_line(clean_obj* world) {
    size_t length = 0, capacity = 128;
    char* line = clean_stdio_malloc(capacity);
    flockfile(stdout);
    for (int c; (c = getc_unlocked(stdout)) != EOF;) {
        if (length == capacity) {
            if (capacity > SIZE_MAX / 2) clean_panic("IO.FS.Handle.getLine: line too large");
            capacity *= 2;
            char* longer = realloc(line, capacity);
            if (!longer) clean_panic("IO.FS.Handle.getLine: allocation failed");
            line = longer;
        }
        line[length++] = (char)c;
        if (c == '\n') break;
    }
    int error = errno;
    funlockfile(stdout);
    clean_obj* result;
    if (ferror(stdout))
        result = clean_stdio_error(error, world);
    else {
        if (feof(stdout)) clearerr(stdout);
        result = clean_stdio_ok(clean_stdio_line_text(line, length), world);
    }
    free(line);
    return result;
}

static clean_obj* clean_stdio_default_stdout(void) {
    return clean_alloc_ctor(0, 6, 0,
        clean_alloc_closure((void*)clean_stdout_flush, 1, 0),
        clean_alloc_closure((void*)clean_stdout_read, 2, 0),
        clean_alloc_closure((void*)clean_stdout_write, 2, 0),
        clean_alloc_closure((void*)clean_stdout_get_line, 1, 0),
        clean_alloc_closure((void*)clean_stdout_put_str, 2, 0),
        clean_alloc_closure((void*)clean_stdout_is_tty, 1, 0));
}

static pthread_once_t clean_stdio_once = PTHREAD_ONCE_INIT;
static pthread_key_t clean_stdio_key;

static void clean_stdio_release_slot(void* value) {
    if (value) clean_dec((clean_obj*)value);
}

static void clean_stdio_init_key(void) {
    if (pthread_key_create(&clean_stdio_key, clean_stdio_release_slot))
        clean_panic("IO.getStdout: failed to initialize the thread-local stream");
}

static clean_obj* clean_stdio_current_stdout(void) {
    if (pthread_once(&clean_stdio_once, clean_stdio_init_key))
        clean_panic("IO.getStdout: failed to access the thread-local stream");
    clean_obj* stream = pthread_getspecific(clean_stdio_key);
    if (!stream) {
        stream = clean_stdio_default_stdout();
        if (pthread_setspecific(clean_stdio_key, stream))
            clean_panic("IO.getStdout: failed to retain the thread-local stream");
    }
    return stream;
}

/* BaseIO returns ST.Out, whose only physical field is the stream after world erasure. */
static clean_obj* clean_stdio_stream_state(clean_obj* stream, clean_obj* world) {
#ifdef CLEAN_STDIO_ERASED_WORLD
    clean_dec(world);
    return stream;
#else
    return clean_stdio_ok(stream, world);
#endif
}

static clean_obj* clean_stdio_get_stdout(clean_obj* world) {
    clean_obj* stream = clean_stdio_current_stdout();
    clean_inc(stream);
    return clean_stdio_stream_state(stream, world);
}

static clean_obj* clean_stdio_set_stdout(clean_obj* replacement, clean_obj* world) {
    clean_obj* previous = clean_stdio_current_stdout();
    if (pthread_setspecific(clean_stdio_key, replacement))
        clean_panic("IO.setStdout: failed to replace the thread-local stream");
    return clean_stdio_stream_state(previous, world);
}
