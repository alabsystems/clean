#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/metrics.rs `DeadlineOwner`, `EventWakeKind` (the `label_enum!`
// expansions' enums: derives and accessor impls dropped), `wake_owner`
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
pub const fn wake_owner(kind: EventWakeKind, deadline_owner: DeadlineOwner) -> DeadlineOwner {
    if matches!(kind, EventWakeKind::Timer) {
        deadline_owner
    } else {
        DeadlineOwner::None
    }
}
/// aterm-gui SPECS.md m-wake-owner, its second half: ∀ k, o: k ≠ Timer ⇒ wake_owner(k, o) =
/// DeadlineOwner::None (the first half, k = Timer, is `pm1_wake_owner_timer.rs`'s: the clause
/// is split over two artifacts, each within the reference entry's heartbeat budget).
pub fn wake_owner_other_spec(kind: EventWakeKind, deadline_owner: DeadlineOwner) -> u8 {
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
    let ok = timer || matches!(result, DeadlineOwner::None);
    let z = ok as u8;
    z - 1 + 1
}
