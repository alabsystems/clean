#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/menu.rs `MenuAction` (derives dropped), `requires_terminal_tab`
// (its `#[cfg(any(target_os = "macos", test))]` holds on this triple)
pub enum MenuAction {
    About,
    SoftwareUpdate,
    Version,
    ApplyUpdate,
    Preferences,
    Quit,
    NewWindow,
    NewTab,
    OpenMarkdown,
    OpenEditor,
    Save,
    ReopenClosedTab,
    ReopenClosedView,
    MoveTabToNewWindow,
    MoveTabToNextWindow,
    ViewSessionInNewWindow,
    CloseTab,
    Copy,
    Paste,
    SelectAll,
    Find,
    FindNext,
    FindPrev,
    ToggleFullScreen,
    FontIncrease,
    FontDecrease,
    FontActualSize,
    SplitVertical,
    SplitHorizontal,
    ToggleMatrixRain,
    FavouriteKitty,
    NextKitty,
    ToggleSeriousMode,
    ToggleSettings,
    ToggleNeedsInWindows,
    StatsBarsDeck,
    StatsBarsSill,
    StatsBarsOff,
    DeckSizeAuto,
    DeckSizeFull,
    DeckSizeFolded,
    ToggleStatsLens,
    NetworkState,
    RewindPane,
    ExportPaneHistory,
    ForgetPaneHistory,
    ForgetAllHistory,
    Packages,
    Messages,
    SystemState,
    OpenPalette,
    ChooseTheme,
    BrowseThemes,
    ChooseTabTheme,
    ClearTabTheme,
    CopySessionId,
    CopyCwd,
    Overview,
    NextNeed,
    HarnessLog,
    TakeOver,
    HandBack,
    ReadThisMac,
    ReadFleet,
    SummarizeFleet,
    FabricStatus,
    FabricOn,
    FabricOff,
    FleetMachines,
    RenameSession,
    SetRole,
    ResetTerminal,
    HarnessSettings,
    Minimize,
    Zoom,
    NextTab,
    PrevTab,
    Help,
}
#[cfg(any(target_os = "macos", test))]
pub const fn requires_terminal_tab(action: MenuAction) -> bool {
    matches!(
        action,
        MenuAction::SplitVertical
            | MenuAction::SplitHorizontal
            | MenuAction::ViewSessionInNewWindow
            | MenuAction::ToggleMatrixRain
            | MenuAction::RenameSession
            | MenuAction::HarnessLog
            | MenuAction::TakeOver
            | MenuAction::HandBack
            | MenuAction::SetRole
            | MenuAction::ResetTerminal
            | MenuAction::ChooseTabTheme
            | MenuAction::ClearTabTheme
            | MenuAction::RewindPane
            | MenuAction::ExportPaneHistory
            | MenuAction::ForgetPaneHistory
    )
}
/// aterm-gui SPECS.md menu-requires-terminal (the set equation): requires_terminal_tab(a) ⇔ a ∈
/// {SplitVertical, SplitHorizontal, ViewSessionInNewWindow, ToggleMatrixRain, RenameSession,
/// HarnessLog, TakeOver, HandBack, SetRole, ResetTerminal, ChooseTabTheme, ClearTabTheme,
/// RewindPane, ExportPaneHistory, ForgetPaneHistory} (15 actions).
pub fn requires_terminal_tab_spec(action: MenuAction) -> u8 {
    let result = matches!(
        action,
        MenuAction::SplitVertical
            | MenuAction::SplitHorizontal
            | MenuAction::ViewSessionInNewWindow
            | MenuAction::ToggleMatrixRain
            | MenuAction::RenameSession
            | MenuAction::HarnessLog
            | MenuAction::TakeOver
            | MenuAction::HandBack
            | MenuAction::SetRole
            | MenuAction::ResetTerminal
            | MenuAction::ChooseTabTheme
            | MenuAction::ClearTabTheme
            | MenuAction::RewindPane
            | MenuAction::ExportPaneHistory
            | MenuAction::ForgetPaneHistory
    );
    let want = match action {
        MenuAction::About => false,
        MenuAction::SoftwareUpdate => false,
        MenuAction::Version => false,
        MenuAction::ApplyUpdate => false,
        MenuAction::Preferences => false,
        MenuAction::Quit => false,
        MenuAction::NewWindow => false,
        MenuAction::NewTab => false,
        MenuAction::OpenMarkdown => false,
        MenuAction::OpenEditor => false,
        MenuAction::Save => false,
        MenuAction::ReopenClosedTab => false,
        MenuAction::ReopenClosedView => false,
        MenuAction::MoveTabToNewWindow => false,
        MenuAction::MoveTabToNextWindow => false,
        MenuAction::ViewSessionInNewWindow => true,
        MenuAction::CloseTab => false,
        MenuAction::Copy => false,
        MenuAction::Paste => false,
        MenuAction::SelectAll => false,
        MenuAction::Find => false,
        MenuAction::FindNext => false,
        MenuAction::FindPrev => false,
        MenuAction::ToggleFullScreen => false,
        MenuAction::FontIncrease => false,
        MenuAction::FontDecrease => false,
        MenuAction::FontActualSize => false,
        MenuAction::SplitVertical => true,
        MenuAction::SplitHorizontal => true,
        MenuAction::ToggleMatrixRain => true,
        MenuAction::FavouriteKitty => false,
        MenuAction::NextKitty => false,
        MenuAction::ToggleSeriousMode => false,
        MenuAction::ToggleSettings => false,
        MenuAction::ToggleNeedsInWindows => false,
        MenuAction::StatsBarsDeck => false,
        MenuAction::StatsBarsSill => false,
        MenuAction::StatsBarsOff => false,
        MenuAction::DeckSizeAuto => false,
        MenuAction::DeckSizeFull => false,
        MenuAction::DeckSizeFolded => false,
        MenuAction::ToggleStatsLens => false,
        MenuAction::NetworkState => false,
        MenuAction::RewindPane => true,
        MenuAction::ExportPaneHistory => true,
        MenuAction::ForgetPaneHistory => true,
        MenuAction::ForgetAllHistory => false,
        MenuAction::Packages => false,
        MenuAction::Messages => false,
        MenuAction::SystemState => false,
        MenuAction::OpenPalette => false,
        MenuAction::ChooseTheme => false,
        MenuAction::BrowseThemes => false,
        MenuAction::ChooseTabTheme => true,
        MenuAction::ClearTabTheme => true,
        MenuAction::CopySessionId => false,
        MenuAction::CopyCwd => false,
        MenuAction::Overview => false,
        MenuAction::NextNeed => false,
        MenuAction::HarnessLog => true,
        MenuAction::TakeOver => true,
        MenuAction::HandBack => true,
        MenuAction::ReadThisMac => false,
        MenuAction::ReadFleet => false,
        MenuAction::SummarizeFleet => false,
        MenuAction::FabricStatus => false,
        MenuAction::FabricOn => false,
        MenuAction::FabricOff => false,
        MenuAction::FleetMachines => false,
        MenuAction::RenameSession => true,
        MenuAction::SetRole => true,
        MenuAction::ResetTerminal => true,
        MenuAction::HarnessSettings => false,
        MenuAction::Minimize => false,
        MenuAction::Zoom => false,
        MenuAction::NextTab => false,
        MenuAction::PrevTab => false,
        MenuAction::Help => false,
    };
    let ok = result == want;
    let z = ok as u8;
    z - 1 + 1
}
