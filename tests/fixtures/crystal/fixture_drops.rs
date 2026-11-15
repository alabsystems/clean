//! Crystal D6 fixture battery (2026-09-24): the double-drop shapes, observed at RUN TIME.
//! Each arm prints an exact line; the runner compares the bytes with the flip-off control.
//!
//! ONE source, BOTH panic strategies, switched on the stable `cfg(panic = "...")`:
//!
//! * `panic=abort` builds `no_std` + `no_main`: the lane's sealed sysroot ships a `panic_abort`
//!   runtime that is not built for `panic=abort`, so no std binary links there, and abort is the
//!   strategy that shipped the miscompile. `core` + `alloc` need no panic runtime. Allocation
//!   goes through libc malloc/free (so a double free is caught by malloc), output through
//!   write(2).
//! * `panic=unwind` builds with std, against that same sysroot (built for unwind). A `no_std`
//!   binary cannot use unwind without the unstable `eh_personality` lang item, and the drop
//!   question D6 asks under unwind is about the same five arms, not about the scaffolding. std's
//!   allocator on macOS is the system malloc, so a double free still traps.
//!
//! The five arms below the scaffolding are shared verbatim.
#![cfg_attr(panic = "abort", no_std)]
#![cfg_attr(panic = "abort", no_main)]
extern crate alloc;
use alloc::string::String;
#[cfg(panic = "abort")]
use core::fmt::Write;
use core::sync::atomic::{AtomicUsize, Ordering};

#[cfg(panic = "abort")]
mod abort_rt {
    #[link(name = "System")]
    unsafe extern "C" {
        fn malloc(n: usize) -> *mut u8;
        fn free(p: *mut u8);
        pub(crate) fn write(fd: i32, buf: *const u8, n: usize) -> isize;
        fn abort() -> !;
    }
    struct Libc;
    unsafe impl core::alloc::GlobalAlloc for Libc {
        unsafe fn alloc(&self, l: core::alloc::Layout) -> *mut u8 {
            // SAFETY: every layout this fixture allocates has align <= 16, which malloc satisfies.
            unsafe { malloc(l.size()) }
        }
        unsafe fn dealloc(&self, p: *mut u8, _l: core::alloc::Layout) {
            // SAFETY: `p` came from `malloc` above.
            unsafe { free(p) }
        }
    }
    #[global_allocator]
    static A: Libc = Libc;
    #[panic_handler]
    fn on_panic(_: &core::panic::PanicInfo) -> ! {
        // SAFETY: abort never returns.
        unsafe { abort() }
    }

    /// The sealed sysroot's `liballoc` was compiled for unwind and names the personality routine.
    /// Under `panic=abort` nothing unwinds, so it is never called; it only has to link.
    #[unsafe(no_mangle)]
    pub extern "C" fn rust_eh_personality() {}

    pub(crate) struct Out {
        pub(crate) buf: [u8; 256],
        pub(crate) n: usize,
    }
    impl core::fmt::Write for Out {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            for &b in s.as_bytes() {
                if self.n < self.buf.len() {
                    self.buf[self.n] = b;
                    self.n += 1;
                }
            }
            Ok(())
        }
    }
}
#[cfg(panic = "abort")]
macro_rules! println {
    ($($t:tt)*) => {{
        let mut o = abort_rt::Out { buf: [0; 256], n: 0 };
        let _ = writeln!(o, $($t)*);
        // SAFETY: fd 1, a buffer of `o.n` initialized bytes.
        unsafe { abort_rt::write(1, o.buf.as_ptr(), o.n) };
    }};
}

static DROPS: AtomicUsize = AtomicUsize::new(0);

pub struct E(pub u64);
impl Drop for E {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

#[inline(never)]
fn tick(fail: bool) -> Result<(), E> {
    if fail { Err(E(7)) } else { Ok(()) }
}

#[inline(never)]
fn fast(x: u64) -> Result<u64, E> {
    Ok(x + 1)
}

/// (i) infer_type's exact shape: `?` over an error whose Drop is observable.
#[inline(never)]
pub fn arm_i(fail: bool, x: u64) -> Result<u64, E> {
    tick(fail)?;
    fast(x)
}

#[inline(never)]
fn g(fail: bool) -> Result<(), String> {
    if fail { Err(String::from("boom-heap-allocated-error")) } else { Ok(()) }
}

/// (ii) a String error: a double drop is a double free, which malloc aborts on.
#[inline(never)]
pub fn arm_ii(fail: bool) -> Result<u64, String> {
    g(fail)?;
    Ok(3)
}

#[inline(never)]
fn mk(fail: bool) -> Result<String, E> {
    if fail { Err(E(9)) } else { Ok(String::from("abcdef")) }
}

/// (iii) the `?` value bound to a Drop-bearing local.
#[inline(never)]
pub fn arm_iii(fail: bool) -> Result<usize, E> {
    let s: String = mk(fail)?;
    Ok(s.len())
}

/// (iv) a call-free Drop-bearing value live across an overflow Assert, consumed by the
/// return aggregate.
#[inline(never)]
pub fn arm_iv(a: u32, b: u32, e: E) -> (E, u32) {
    (e, a + b)
}

/// (v) infer_type's EXACT shape: `&self` methods, `self.tick()?; self.fast(e)`, with an error
/// whose Drop is observable. This is the arm the retired cite stack must double-drop at run time.
pub struct Tc {
    pub budget: u64,
}
impl Tc {
    #[inline(never)]
    fn tick_heartbeat(&self) -> Result<(), E> {
        if self.budget == 0 { Err(E(11)) } else { Ok(()) }
    }
    #[inline(never)]
    fn infer_type_fast(&self, e: &u64) -> Result<u64, E> {
        Ok(*e + self.budget)
    }
    #[inline(never)]
    pub fn infer_type(&self, e: &u64) -> Result<u64, E> {
        self.tick_heartbeat()?;
        self.infer_type_fast(e)
    }
}

#[cfg(panic = "abort")]
#[unsafe(no_mangle)]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    run()
}

#[cfg(not(panic = "abort"))]
fn main() {
    std::process::exit(run());
}

fn run() -> i32 {
    let d0 = DROPS.load(Ordering::SeqCst);
    let r = arm_i(true, 1);
    let ok = matches!(r, Err(E(7)));
    drop(r);
    println!("i-err ok={} drops={}", ok, DROPS.load(Ordering::SeqCst) - d0);
    let d0 = DROPS.load(Ordering::SeqCst);
    let r = arm_i(false, 41);
    println!("i-ok val={:?} drops={}", r.as_ref().ok(), DROPS.load(Ordering::SeqCst) - d0);
    drop(r);

    let r = arm_ii(true);
    println!("ii-err {:?}", r.as_ref().err());
    drop(r);
    println!("ii-ok {:?}", arm_ii(false).ok());

    let d0 = DROPS.load(Ordering::SeqCst);
    let r = arm_iii(true);
    let ok = matches!(r, Err(E(9)));
    drop(r);
    println!("iii-err ok={} drops={}", ok, DROPS.load(Ordering::SeqCst) - d0);
    println!("iii-ok {:?}", arm_iii(false).ok());

    let d0 = DROPS.load(Ordering::SeqCst);
    let (e, s) = arm_iv(2, 3, E(1));
    println!("iv sum={} e={} drops_before={}", s, e.0, DROPS.load(Ordering::SeqCst) - d0);
    drop(e);
    println!("iv drops_after={}", DROPS.load(Ordering::SeqCst) - d0);
    let d0 = DROPS.load(Ordering::SeqCst);
    let r = Tc { budget: 0 }.infer_type(&5);
    let ok = matches!(r, Err(E(11)));
    drop(r);
    println!("v-err ok={} drops={}", ok, DROPS.load(Ordering::SeqCst) - d0);
    println!("v-ok {:?}", Tc { budget: 2 }.infer_type(&5).ok());
    println!("END");
    0
}
