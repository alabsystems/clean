// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Nat values for emitted Rust. Wider values use the existing immutable
//! External object and finalizer machinery, not constructor scalar bytes.

use super::array::alloc_external;
use super::ctor_scalar::alloc_ctor_uninit;
use crate::object_model::{
    is_scalar, lean_box, lean_panic, lean_unbox, CleanExternalClass, CleanObj, ExternalObj,
    LeanObjPtr, ObjKind, MAX_SMALL,
};

unsafe fn finalize_words(data: *mut ()) {
    // SAFETY: only from_limbs installs this class, with exactly this Box type;
    // canonical RC invokes the finalizer once, after the last reference.
    unsafe { drop(Box::from_raw(data.cast::<Vec<u64>>())) };
    #[cfg(test)]
    LIVE_WIDE.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
}

static NAT_CLASS: CleanExternalClass = CleanExternalClass {
    finalize: Some(finalize_words),
    foreach: None,
};

/// Copy borrowed little-endian limbs into a canonical owned Nat.
pub(super) fn from_limbs(words: &[u64]) -> LeanObjPtr {
    let count = words
        .iter()
        .rposition(|word| *word != 0)
        .map_or(0, |i| i + 1);
    let words = &words[..count];
    match words {
        [] => lean_box(0),
        [word] if *word <= MAX_SMALL as u64 => lean_box(*word as usize),
        [..] if count <= 2 => {
            let result = alloc_ctor_uninit(0, 0, 16);
            // SAFETY: the fresh constructor has no object fields and exactly
            // two u64 scalar slots. Unaligned access also works on 32-bit hosts.
            unsafe {
                let data = CleanObj::scalar_ptr(result).cast::<u64>();
                data.write_unaligned(words[0]);
                data.add(1)
                    .write_unaligned(words.get(1).copied().unwrap_or(0));
            }
            result
        }
        _ => {
            let data = Box::into_raw(Box::new(words.to_vec())).cast::<()>();
            // SAFETY: NAT_CLASS is static; its finalizer owns the fresh Vec.
            let result = unsafe { alloc_external(&NAT_CLASS, data) };
            #[cfg(test)]
            LIVE_WIDE.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            result
        }
    }
}

/// Borrow a live runtime object and copy its canonical Nat words.
///
/// # Safety
/// `value` must be a live tagged scalar or runtime heap object. Non-Nat
/// object kinds/classes/layouts are refused before reading their payload.
pub(super) unsafe fn to_limbs(value: LeanObjPtr) -> Vec<u64> {
    if is_scalar(value) {
        let n = lean_unbox(value) as u64;
        return if n == 0 { Vec::new() } else { vec![n] };
    }
    // SAFETY: the caller provides a live heap object. Read its kind before
    // selecting any payload; reject foreign External classes and ctor fields.
    let mut words = unsafe {
        match ObjKind::from_u8((*value).header.kind) {
            ObjKind::Ctor if (*value).header.num_objs == 0 => {
                let data = CleanObj::scalar_ptr(value);
                match (*value).header.scalar_sz {
                    4 => vec![u64::from(data.cast::<u32>().read_unaligned())],
                    8 => vec![data.cast::<u64>().read_unaligned()],
                    16 => vec![
                        data.cast::<u64>().read_unaligned(),
                        data.cast::<u64>().add(1).read_unaligned(),
                    ],
                    _ => lean_panic("invalid Rust Nat constructor layout"),
                }
            }
            ObjKind::External => {
                let external = &*value.cast::<ExternalObj>();
                if !std::ptr::eq(external.class, &NAT_CLASS) || external.data.is_null() {
                    lean_panic("invalid Rust Nat external class");
                }
                (*external.data.cast::<Vec<u64>>()).clone()
            }
            _ => lean_panic("invalid Rust Nat carrier"),
        }
    };
    while words.last() == Some(&0) {
        words.pop();
    }
    words
}

/// Borrow the low word without allocating, including the tagged/two-word
/// boundary and this module's immutable wide payload.
///
/// # Safety
/// `value` must be a live runtime object or tagged scalar.
pub(super) unsafe fn low_word(value: LeanObjPtr) -> u64 {
    if is_scalar(value) {
        return lean_unbox(value) as u64;
    }
    // SAFETY: caller keeps the heap object live. Each payload is read only
    // after checking its exact kind, field count, extent or External class.
    unsafe {
        match ObjKind::from_u8((*value).header.kind) {
            ObjKind::Ctor if (*value).header.num_objs == 0 => {
                let data = CleanObj::scalar_ptr(value);
                match (*value).header.scalar_sz {
                    4 => u64::from(data.cast::<u32>().read_unaligned()),
                    8 | 16 => data.cast::<u64>().read_unaligned(),
                    _ => lean_panic("invalid Rust Nat constructor layout"),
                }
            }
            ObjKind::External => {
                let external = &*value.cast::<ExternalObj>();
                if !std::ptr::eq(external.class, &NAT_CLASS) || external.data.is_null() {
                    lean_panic("invalid Rust Nat external class");
                }
                (*external.data.cast::<Vec<u64>>())
                    .first()
                    .copied()
                    .unwrap_or(0)
            }
            _ => lean_panic("invalid Rust Nat carrier"),
        }
    }
}

/// Consume one `hi` reference and return `hi * 2^64 + lo`.
///
/// # Safety
/// `hi` must be a live runtime object, owned by the caller. A retained alias
/// is independent: copy its words before dropping only this reference.
pub(super) unsafe fn limb_step(hi: LeanObjPtr, lo: u64) -> LeanObjPtr {
    // SAFETY: the caller's reference keeps hi live while its words are copied.
    let mut words = unsafe { to_limbs(hi) };
    words.insert(0, lo);
    let result = from_limbs(&words);
    crate::rc_core::dec(hi);
    result
}

#[cfg(test)]
static LIVE_WIDE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::{clean_alloc_closure, clean_alloc_ctor, clean_dec, clean_inc};
    use std::sync::{atomic::Ordering, Mutex};

    static TEST_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn nat_constructors_keep_small_two_word_and_arbitrary_boundaries() {
        let _lock = TEST_LOCK.lock().unwrap();
        for input in [
            vec![],
            vec![1],
            vec![MAX_SMALL as u64],
            vec![u64::MAX],
            vec![0, 1],
            vec![u64::MAX, u64::MAX],
            vec![0, 0, 1],
            vec![19, 1, 0, 1],
            vec![u64::MAX; 2048],
            vec![7, 0, 0, 0],
        ] {
            let mut expected = input.clone();
            while expected.last() == Some(&0) {
                expected.pop();
            }
            let value = from_limbs(&input);
            // SAFETY: from_limbs returned the caller's owned live Nat.
            assert_eq!(unsafe { to_limbs(value) }, expected);
            clean_dec(value);
        }
        assert_eq!(LIVE_WIDE.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn nat_step_consumes_one_reference_and_preserves_retained_alias() {
        let _lock = TEST_LOCK.lock().unwrap();
        let input = from_limbs(&[19, 1, 0, 1]);
        clean_inc(input);
        // SAFETY: one reference is transferred; the retained alias stays live.
        let result = unsafe { limb_step(input, u64::MAX) };
        assert_eq!(unsafe { to_limbs(input) }, vec![19, 1, 0, 1]);
        assert_eq!(unsafe { to_limbs(result) }, vec![u64::MAX, 19, 1, 0, 1]);
        assert_eq!(LIVE_WIDE.load(Ordering::SeqCst), 2);
        clean_dec(input);
        assert_eq!(LIVE_WIDE.load(Ordering::SeqCst), 1);
        clean_dec(result);
        assert_eq!(LIVE_WIDE.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn nat_payloads_follow_constructor_and_closure_ownership() {
        let _lock = TEST_LOCK.lock().unwrap();
        let value = from_limbs(&[0, 0, 1]);
        // SAFETY: the constructor takes ownership of its one live field.
        let parent = clean_alloc_ctor(0, 1, 0, &[value]);
        clean_dec(parent);
        assert_eq!(LIVE_WIDE.load(Ordering::SeqCst), 0);
        extern "C" fn keep(first: LeanObjPtr, second: LeanObjPtr) -> LeanObjPtr {
            clean_dec(second);
            first
        }
        let value = from_limbs(&[1, 0, 1]);
        // SAFETY: valid two-argument function and one owned captured value.
        let closure = clean_alloc_closure(keep as *const (), 2, &[value]);
        clean_dec(closure);
        assert_eq!(LIVE_WIDE.load(Ordering::SeqCst), 0);
    }
}
