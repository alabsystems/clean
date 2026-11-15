#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_launch_gates.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

/// The clause without `¬tty`: false at (false, true).
pub fn launch_alert_wanted_wrong(headless: bool, stderr_is_tty: bool) -> u8 {
    let result = !headless && !stderr_is_tty;
    let ok = result == !headless;
    let z = ok as u8;
    z - 1 + 1
}
pub enum LinuxTrialStart {
    Window,
    WindowOnceOpen,
    Session,
}
/// The clause with WindowOnceOpen when the display answers: false at (false, true).
pub fn linux_trial_start_wrong(headless: bool, display_answers: bool) -> u8 {
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
        matches!(result, LinuxTrialStart::WindowOnceOpen)
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
/// The clause without `cfg(windows)`: false at SettingsBurst.
pub fn resample_wants_repair_frame_wrong(cause: ResampleCause) -> u8 {
    let result = cfg!(windows) && matches!(cause, ResampleCause::SettingsBurst);
    let ok = {
        let burst = match cause {
            ResampleCause::SettingsBurst => true,
            ResampleCause::Poll => false,
        };
        result == burst
    };
    let z = ok as u8;
    z - 1 + 1
}
