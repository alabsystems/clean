#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_wake_owner.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

pub enum DeadlineOwner {
    None,
    BootHealth,
    PendingReveal,
    Blink,
    BellFlash,
    SyncHold,
    Autoscroll,
    ResizeSettle,
    PresentRetry,
    FrameCap,
    CursorEffect,
    Rain,
    NativePreview,
    Predictor,
    ScrollGlide,
    Overscroll,
    ScrollPill,
    WordDecorations,
    LevelUp,
    AutoApply,
    ReaderResume,
    UpgradeRealized,
    WakeHeal,
    Video,
    SessionChrome,
    TitleDrift,
    KittyTenure,
    MessageBand,
    SessionStatus,
    ConsentCard,
    Presence,
    HandoffPark,
    MessageBandMotion,
    SessionWaits,
    AosEchoHold,
    InputWatch,
    CrashJournal,
    UpdateChecker,
    SplitRegridHold,
    KittyAnimation,
    RenderEpoch,
    DebuggerChange,
    DevToolsHandOver,
    ClaudeCard,
    ThemePreview,
    OverviewFabric,
    SessionLog,
    HarnessActs,
    AutopilotTimer,
    ConsentObserver,
    Spare,
    OutputCadence,
    SystemVitals,
    StatsLens,
    AgentsPanel,
    StatsLive,
    StatsNeedle,
    NativeMotion,
}
pub enum EventWakeKind {
    None,
    Init,
    Poll,
    Timer,
    WaitCancelled,
}
/// The second half without its `k ≠ Timer`: false at (Timer, Blink).
pub fn wake_owner_other_wrong(kind: EventWakeKind, deadline_owner: DeadlineOwner) -> u8 {
    let timer = match kind {
        EventWakeKind::None => false,
        EventWakeKind::Init => false,
        EventWakeKind::Poll => false,
        EventWakeKind::Timer => true,
        EventWakeKind::WaitCancelled => false,
    };
    let result = if matches!(kind, EventWakeKind::Timer) {
        deadline_owner
    } else {
        DeadlineOwner::None
    };
    let ok = matches!(result, DeadlineOwner::None);
    let z = ok as u8;
    z - 1 + 1
}
