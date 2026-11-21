/* Copyright 2026 Andrew Yates
 * SPDX-License-Identifier: Apache-2.0
 *
 * lean_decode_io_error(code, NULL) from Lean 4.36 on Darwin. The source
 * classifies CRT errno through libuv, including its approximations for
 * errors libuv cannot represent. The compiler checks the IO.Error tags
 * and field layouts before materializing these constructor values.
 */
static clean_obj* clean_stdio_errno_payload(int code) {
    unsigned tag = CLEAN_STDIO_OTHER_ERROR;
    const char* text = NULL;
    switch (code) {
    case EPERM: tag = CLEAN_STDIO_PERMISSION_DENIED; text = "operation not permitted"; break;
    case ENOENT: tag = CLEAN_STDIO_NO_FILE_OR_DIRECTORY; text = "no such file or directory"; break;
    case ESRCH: tag = CLEAN_STDIO_NO_SUCH_THING; text = "no such process"; break;
    case EINTR: tag = CLEAN_STDIO_INTERRUPTED; text = "interrupted system call"; break;
    case EIO: tag = CLEAN_STDIO_HARDWARE_FAULT; text = "i/o error"; break;
    case ENXIO: tag = CLEAN_STDIO_NO_SUCH_THING; text = "no such device or address"; break;
    case E2BIG: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "argument list too long"; break;
    case ENOEXEC: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "exec format error"; break;
    case EBADF: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "bad file descriptor"; break;
    case ECHILD: tag = CLEAN_STDIO_NO_SUCH_THING; text = "no such process"; break;
    case EDEADLK: tag = CLEAN_STDIO_RESOURCE_BUSY; text = "resource busy or locked"; break;
    case ENOMEM: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "not enough memory"; break;
    case EACCES: tag = CLEAN_STDIO_PERMISSION_DENIED; text = "permission denied"; break;
    case EFAULT: tag = CLEAN_STDIO_OTHER_ERROR; text = "bad address in system call argument"; break;
    case EBUSY: tag = CLEAN_STDIO_RESOURCE_BUSY; text = "resource busy or locked"; break;
    case EEXIST: tag = CLEAN_STDIO_ALREADY_EXISTS; text = "file already exists"; break;
    case EXDEV: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "cross-device link not permitted"; break;
    case ENODEV: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "no such device"; break;
    case ENOTDIR: tag = CLEAN_STDIO_INAPPROPRIATE_TYPE; text = "not a directory"; break;
    case EISDIR: tag = CLEAN_STDIO_INAPPROPRIATE_TYPE; text = "illegal operation on a directory"; break;
    case EINVAL: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "invalid argument"; break;
    case ENFILE: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "file table overflow"; break;
    case EMFILE: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "too many open files"; break;
    case ENOTTY: tag = CLEAN_STDIO_ILLEGAL_OPERATION; text = "inappropriate ioctl for device"; break;
    case ETXTBSY: tag = CLEAN_STDIO_RESOURCE_BUSY; text = "text file is busy"; break;
    case EFBIG: tag = CLEAN_STDIO_PERMISSION_DENIED; text = "file too large"; break;
    case ENOSPC: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "no space left on device"; break;
    case ESPIPE: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "invalid seek"; break;
    case EROFS: tag = CLEAN_STDIO_PERMISSION_DENIED; text = "read-only file system"; break;
    case EMLINK: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "too many links"; break;
    case EPIPE: tag = CLEAN_STDIO_RESOURCE_VANISHED; text = "broken pipe"; break;
    case EDOM: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "invalid argument"; break;
    case ERANGE: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "result too large"; break;
    case EAGAIN: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "resource temporarily unavailable"; break;
    case EINPROGRESS: tag = CLEAN_STDIO_ALREADY_EXISTS; text = "socket is already connected"; break;
    case EALREADY: tag = CLEAN_STDIO_OTHER_ERROR; text = "connection already in progress"; break;
    case ENOTSOCK: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "socket operation on non-socket"; break;
    case EDESTADDRREQ: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "destination address required"; break;
    case EMSGSIZE: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "message too long"; break;
    case EPROTOTYPE: tag = CLEAN_STDIO_PROTOCOL_ERROR; text = "protocol wrong type for socket"; break;
    case ENOPROTOOPT: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "protocol not available"; break;
    case EPROTONOSUPPORT: tag = CLEAN_STDIO_PROTOCOL_ERROR; text = "protocol not supported"; break;
    case ESOCKTNOSUPPORT: tag = CLEAN_STDIO_OTHER_ERROR; text = "socket type not supported"; break;
    case ENOTSUP: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "operation not supported on socket"; break;
    case EAFNOSUPPORT: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "address family not supported"; break;
    case EADDRINUSE: tag = CLEAN_STDIO_RESOURCE_BUSY; text = "address already in use"; break;
    case EADDRNOTAVAIL: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "address not available"; break;
    case ENETDOWN: tag = CLEAN_STDIO_RESOURCE_VANISHED; text = "network is down"; break;
    case ENETUNREACH: tag = CLEAN_STDIO_NO_SUCH_THING; text = "network is unreachable"; break;
    case ENETRESET: tag = CLEAN_STDIO_RESOURCE_VANISHED; text = "connection reset by peer"; break;
    case ECONNABORTED: tag = CLEAN_STDIO_PERMISSION_DENIED; text = "software caused connection abort"; break;
    case ECONNRESET: tag = CLEAN_STDIO_RESOURCE_VANISHED; text = "connection reset by peer"; break;
    case ENOBUFS: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "no buffer space available"; break;
    case EISCONN: tag = CLEAN_STDIO_ALREADY_EXISTS; text = "socket is already connected"; break;
    case ENOTCONN: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "socket is not connected"; break;
    case ESHUTDOWN: tag = CLEAN_STDIO_OTHER_ERROR; text = "cannot send after transport endpoint shutdown"; break;
    case ETIMEDOUT: tag = CLEAN_STDIO_TIME_EXPIRED; text = "connection timed out"; break;
    case ECONNREFUSED: tag = CLEAN_STDIO_NO_SUCH_THING; text = "connection refused"; break;
    case ELOOP: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "too many symbolic links encountered"; break;
    case ENAMETOOLONG: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "name too long"; break;
    case EHOSTDOWN: tag = CLEAN_STDIO_OTHER_ERROR; text = "host is down"; break;
    case EHOSTUNREACH: tag = CLEAN_STDIO_NO_SUCH_THING; text = "host is unreachable"; break;
    case ENOTEMPTY: tag = CLEAN_STDIO_UNSATISFIED_CONSTRAINTS; text = "directory not empty"; break;
    case ENOLCK: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "resource temporarily unavailable"; break;
    case ENOSYS: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "function not implemented"; break;
    case EFTYPE: tag = CLEAN_STDIO_OTHER_ERROR; text = "inappropriate file type or format"; break;
    case EOVERFLOW: tag = CLEAN_STDIO_OTHER_ERROR; text = "value too large for defined data type"; break;
    case ECANCELED: tag = CLEAN_STDIO_OTHER_ERROR; text = "operation canceled"; break;
    case EIDRM: tag = CLEAN_STDIO_RESOURCE_VANISHED; text = "broken pipe"; break;
    case ENOMSG: tag = CLEAN_STDIO_NO_SUCH_THING; text = "no data available"; break;
    case EILSEQ: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "illegal byte sequence"; break;
    case EBADMSG: tag = CLEAN_STDIO_PROTOCOL_ERROR; text = "protocol error"; break;
    case ENODATA: tag = CLEAN_STDIO_NO_SUCH_THING; text = "no data available"; break;
    case ENOLINK: tag = CLEAN_STDIO_RESOURCE_VANISHED; text = "connection reset by peer"; break;
    case ENOSR: tag = CLEAN_STDIO_RESOURCE_EXHAUSTED; text = "no buffer space available"; break;
    case ENOSTR: tag = CLEAN_STDIO_INVALID_ARGUMENT; text = "invalid argument"; break;
    case EPROTO: tag = CLEAN_STDIO_PROTOCOL_ERROR; text = "protocol error"; break;
    case ETIME: tag = CLEAN_STDIO_TIME_EXPIRED; text = "connection timed out"; break;
    case EOPNOTSUPP: tag = CLEAN_STDIO_UNSUPPORTED_OPERATION; text = "operation not supported on socket"; break;
    case 3000: tag = CLEAN_STDIO_OTHER_ERROR; text = "address family not supported"; break;
    case 3001: tag = CLEAN_STDIO_OTHER_ERROR; text = "temporary failure"; break;
    case 3002: tag = CLEAN_STDIO_OTHER_ERROR; text = "bad ai_flags value"; break;
    case 3003: tag = CLEAN_STDIO_OTHER_ERROR; text = "request canceled"; break;
    case 3004: tag = CLEAN_STDIO_OTHER_ERROR; text = "permanent failure"; break;
    case 3005: tag = CLEAN_STDIO_OTHER_ERROR; text = "ai_family not supported"; break;
    case 3006: tag = CLEAN_STDIO_OTHER_ERROR; text = "out of memory"; break;
    case 3007: tag = CLEAN_STDIO_OTHER_ERROR; text = "no address"; break;
    case 3008: tag = CLEAN_STDIO_OTHER_ERROR; text = "unknown node or service"; break;
    case 3009: tag = CLEAN_STDIO_OTHER_ERROR; text = "argument buffer overflow"; break;
    case 3010: tag = CLEAN_STDIO_OTHER_ERROR; text = "service not available for socket type"; break;
    case 3011: tag = CLEAN_STDIO_OTHER_ERROR; text = "socket type not supported"; break;
    case 3013: tag = CLEAN_STDIO_OTHER_ERROR; text = "invalid value for hints"; break;
    case 3014: tag = CLEAN_STDIO_OTHER_ERROR; text = "resolved protocol is unknown"; break;
    case 4023: tag = CLEAN_STDIO_OTHER_ERROR; text = "protocol driver not attached"; break;
    case 4030: tag = CLEAN_STDIO_OTHER_ERROR; text = "remote I/O error"; break;
    case 4056: tag = CLEAN_STDIO_OTHER_ERROR; text = "machine is not on the network"; break;
    case 4080: tag = CLEAN_STDIO_OTHER_ERROR; text = "invalid Unicode character"; break;
    case 4094: tag = CLEAN_STDIO_OTHER_ERROR; text = "unknown error"; break;
    case 4095: tag = CLEAN_STDIO_OTHER_ERROR; text = "end of file"; break;
    default: break;
    }
    char buffer[64];
    if (!text) {
        snprintf(buffer, sizeof(buffer), "Unknown system error %lld", -(long long)code);
        text = buffer;
    }
    clean_obj* details = clean_mk_string(text);
    clean_obj* error;
    if (tag == CLEAN_STDIO_INTERRUPTED || tag == CLEAN_STDIO_NO_FILE_OR_DIRECTORY) {
        error = clean_alloc_ctor(tag, 2, sizeof(uint32_t), clean_mk_string(""), details);
    } else if (tag == CLEAN_STDIO_ALREADY_EXISTS || tag >= CLEAN_STDIO_INVALID_ARGUMENT) {
        error = clean_alloc_ctor(tag, 2, sizeof(uint32_t), clean_box(0), details);
    } else {
        error = clean_alloc_ctor(tag, 1, sizeof(uint32_t), details);
    }
    clean_ctor_set_uint32(error, error->header.num_objs * sizeof(void*), (uint32_t)code);
    return error;
}
