#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/lib.rs `launch_alert_wanted`; `LinuxTrialStart` (derives dropped)
// and `linux_trial_start` (their `cfg(any(target_os = "linux", test))` dropped: aterm's test
// build on this triple carries them, bodies unchanged); `ResampleCause` (derives dropped) and
// `resample_wants_repair_frame` (the enum as aterm's TEST build compiles it on this triple:
// `Poll`'s `cfg(any(windows, test))` holds there and is dropped here; the release build's
// one-variant enum is laid out untagged, size 0, which SemR's decoder does not read, so that
// shape is not a row; `cfg!(windows)` is false on this triple).
// `win32::attached_console_is_released_for` is `cfg(windows)`: not here (no Windows-triple
// sysroot for the stage-2 compiler).
pub const fn launch_alert_wanted(headless: bool, stderr_is_tty: bool) -> bool {
    !headless && !stderr_is_tty
}
/// aterm-gui SPECS.md launch-boolean-gates: launch_alert_wanted(h, tty) = ¬h ∧ ¬tty.
pub fn launch_alert_wanted_spec(headless: bool, stderr_is_tty: bool) -> u8 {
    let result = !headless && !stderr_is_tty;
    let ok = result == !(headless || stderr_is_tty);
    let z = ok as u8;
    z - 1 + 1
}
pub enum LinuxTrialStart {
    Window,
    WindowOnceOpen,
    Session,
}
pub const fn linux_trial_start(headless: bool, display_answers: bool) -> LinuxTrialStart {
    if headless {
        LinuxTrialStart::Session
    } else if display_answers {
        LinuxTrialStart::Window
    } else {
        LinuxTrialStart::WindowOnceOpen
    }
}
/// aterm-gui SPECS.md launch-boolean-gates: linux_trial_start(h, d) = Session if h, else Window
/// if d, else WindowOnceOpen.
pub fn linux_trial_start_spec(headless: bool, display_answers: bool) -> u8 {
    let result = if headless {
        LinuxTrialStart::Session
    } else if display_answers {
        LinuxTrialStart::Window
    } else {
        LinuxTrialStart::WindowOnceOpen
    };
    let ok = if headless {
        matches!(result, LinuxTrialStart::Session)
    } else if display_answers {
        matches!(result, LinuxTrialStart::Window)
    } else {
        matches!(result, LinuxTrialStart::WindowOnceOpen)
    };
    let z = ok as u8;
    z - 1 + 1
}
#[cfg(any(target_os = "macos", windows, test))]
pub enum ResampleCause {
    SettingsBurst,
    Poll,
}
#[cfg(any(target_os = "macos", windows, test))]
pub const fn resample_wants_repair_frame(cause: ResampleCause) -> bool {
    cfg!(windows) && matches!(cause, ResampleCause::SettingsBurst)
}
/// aterm-gui SPECS.md launch-boolean-gates: resample_wants_repair_frame(c) = cfg(windows) ∧ c =
/// SettingsBurst (here, aarch64-apple-darwin: cfg(windows) is false).
pub fn resample_wants_repair_frame_spec(cause: ResampleCause) -> u8 {
    let result = cfg!(windows) && matches!(cause, ResampleCause::SettingsBurst);
    let ok = {
        let burst = match cause {
            ResampleCause::SettingsBurst => true,
            ResampleCause::Poll => false,
        };
        result == (cfg!(windows) && burst)
    };
    let z = ok as u8;
    z - 1 + 1
}
