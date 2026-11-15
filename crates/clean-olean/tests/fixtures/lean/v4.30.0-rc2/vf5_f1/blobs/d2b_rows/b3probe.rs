// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// B3's second reader for the D-2(b) rows (Clean docs/DECISIONS.md R213): rustc's OWN
// discriminant assignment and discriminant type for each fieldless enum of every row
// artifact's source (and VF7's `bv_creation_flags.rs`), printed by a program the same
// compiler builds without Trust. `b3_rustc.tsv` is its output:
//
//   rustc -Ztrust-verify=off -o b3probe b3probe.rs && ./b3probe > b3_rustc.tsv
#![feature(discriminant_kind)]
#![allow(dead_code, unused_imports)]
#[path = "band_icon.rs"]
mod band_icon;
#[path = "bidi_removed_by_x9.rs"]
mod bidi_removed_by_x9;
#[path = "bridge_decision_resolve.rs"]
mod bridge_decision_resolve;
#[path = "../vf7/bv_creation_flags.rs"]
mod bv_creation_flags;
#[path = "classify_shape.rs"]
mod classify_shape;
#[path = "containment_level.rs"]
mod containment_level;
#[path = "cursor_shown.rs"]
mod cursor_shown;
#[path = "dr_class_grant_stable.rs"]
mod dr_class_grant_stable;
#[path = "family_mode.rs"]
mod family_mode;
#[path = "folder_absent_means_allowed.rs"]
mod folder_absent_means_allowed;
#[path = "http_method.rs"]
mod http_method;
#[path = "image_anchor_grant_unverifiable.rs"]
mod image_anchor_grant_unverifiable;
#[path = "key_event_kitty_value.rs"]
mod key_event_kitty_value;
#[path = "log_record_cap.rs"]
mod log_record_cap;
#[path = "mouse.rs"]
mod mouse;
#[path = "origin_trust_rank.rs"]
mod origin_trust_rank;
#[path = "panel_column.rs"]
mod panel_column;
#[path = "phase_program.rs"]
mod phase_program;
#[path = "pm1_arming.rs"]
mod pm1_arming;
#[path = "pm1_attempt_finish.rs"]
mod pm1_attempt_finish;
#[path = "pm1_blink_clock_armed.rs"]
mod pm1_blink_clock_armed;
#[path = "pm1_boot_health.rs"]
mod pm1_boot_health;
#[path = "pm1_capture_after_present.rs"]
mod pm1_capture_after_present;
#[path = "pm1_carry_ceiling.rs"]
mod pm1_carry_ceiling;
#[path = "pm1_chrome_face.rs"]
mod pm1_chrome_face;
#[path = "pm1_class_rank.rs"]
mod pm1_class_rank;
#[path = "pm1_cli_mark.rs"]
mod pm1_cli_mark;
#[path = "pm1_cli_verb.rs"]
mod pm1_cli_verb;
#[path = "pm1_completion_consent.rs"]
mod pm1_completion_consent;
#[path = "pm1_converge_outcome.rs"]
mod pm1_converge_outcome;
#[path = "pm1_decide_bind.rs"]
mod pm1_decide_bind;
#[path = "pm1_drop_taint.rs"]
mod pm1_drop_taint;
#[path = "pm1_durable_post.rs"]
mod pm1_durable_post;
#[path = "pm1_held_loss.rs"]
mod pm1_held_loss;
#[path = "pm1_launch_gates.rs"]
mod pm1_launch_gates;
#[path = "pm1_leaf_close.rs"]
mod pm1_leaf_close;
#[path = "pm1_lights_mode.rs"]
mod pm1_lights_mode;
#[path = "pm1_lower_role.rs"]
mod pm1_lower_role;
#[path = "pm1_menu_requires_terminal.rs"]
mod pm1_menu_requires_terminal;
#[path = "pm1_menu_tag.rs"]
mod pm1_menu_tag;
#[path = "pm1_menu_tag_inverse.rs"]
mod pm1_menu_tag_inverse;
#[path = "pm1_native_control.rs"]
mod pm1_native_control;
#[path = "pm1_pending_wait.rs"]
mod pm1_pending_wait;
#[path = "pm1_restore_pass.rs"]
mod pm1_restore_pass;
#[path = "pm1_roster_duty.rs"]
mod pm1_roster_duty;
#[path = "pm1_row_state.rs"]
mod pm1_row_state;
#[path = "pm1_seamless.rs"]
mod pm1_seamless;
#[path = "pm1_status_words.rs"]
mod pm1_status_words;
#[path = "pm1_wake_owner.rs"]
mod pm1_wake_owner;
#[path = "pm1_wake_owner_timer.rs"]
mod pm1_wake_owner_timer;
#[path = "pm1_watchdog.rs"]
mod pm1_watchdog;
#[path = "pm1_wheel_route.rs"]
mod pm1_wheel_route;
#[path = "pm1_window_title.rs"]
mod pm1_window_title;
#[path = "presence_due_now.rs"]
mod presence_due_now;
#[path = "qos_clamped.rs"]
mod qos_clamped;
#[path = "reset_kind_takeable.rs"]
mod reset_kind_takeable;
#[path = "reset_offer_shows_button.rs"]
mod reset_offer_shows_button;
#[path = "role_standing.rs"]
mod role_standing;
#[path = "screen_buffer_from_bool.rs"]
mod screen_buffer_from_bool;
#[path = "select_face.rs"]
mod select_face;
#[path = "tccutil.rs"]
mod tccutil;
#[path = "uri_scheme_default_port.rs"]
mod uri_scheme_default_port;
#[path = "vt_decscl_param.rs"]
mod vt_decscl_param;
#[path = "wait_end_echo.rs"]
mod wait_end_echo;
#[path = "waiter.rs"]
mod waiter;
#[path = "watermark.rs"]
mod watermark;
#[path = "wire_kind_carries_fd.rs"]
mod wire_kind_carries_fd;
fn name<T: core::marker::DiscriminantKind>() -> &'static str {
    core::any::type_name::<<T as core::marker::DiscriminantKind>::Discriminant>()
}
fn main() {
    // `<artifact>\t<enum name>\t<rustc's discriminant type>\t<discriminants in declaration order>`
    println!(
        "band_icon\tIcon\t{}\t{:?}",
        name::<band_icon::Icon>(),
        [
            band_icon::Icon::Info as i128,
            band_icon::Icon::Success as i128,
            band_icon::Icon::Warn as i128,
            band_icon::Icon::Error as i128,
            band_icon::Icon::Download as i128,
            band_icon::Icon::Update as i128,
            band_icon::Icon::Upload as i128,
            band_icon::Icon::Pause as i128,
            band_icon::Icon::Sparkle as i128,
            band_icon::Icon::Alert as i128,
            band_icon::Icon::Dot as i128,
            band_icon::Icon::More as i128,
            band_icon::Icon::Remove as i128
        ]
    );
    println!(
        "band_icon\tBandIcon\t{}\t{:?}",
        name::<band_icon::BandIcon>(),
        [
            band_icon::BandIcon::Info as i128,
            band_icon::BandIcon::Success as i128,
            band_icon::BandIcon::Warn as i128,
            band_icon::BandIcon::Error as i128,
            band_icon::BandIcon::Download as i128,
            band_icon::BandIcon::Update as i128,
            band_icon::BandIcon::Upload as i128,
            band_icon::BandIcon::Pause as i128,
            band_icon::BandIcon::Sparkle as i128,
            band_icon::BandIcon::Alert as i128,
            band_icon::BandIcon::Dot as i128,
            band_icon::BandIcon::More as i128,
            band_icon::BandIcon::Remove as i128,
            band_icon::BandIcon::Disc as i128,
            band_icon::BandIcon::Ring as i128,
            band_icon::BandIcon::HalfDisc as i128,
            band_icon::BandIcon::DottedRing as i128,
            band_icon::BandIcon::SlashedRing as i128,
            band_icon::BandIcon::ToBar as i128,
            band_icon::BandIcon::Fisheye as i128,
            band_icon::BandIcon::InsetDiamond as i128,
            band_icon::BandIcon::House as i128,
            band_icon::BandIcon::Diamond as i128,
            band_icon::BandIcon::Lock as i128,
            band_icon::BandIcon::Hourglass as i128,
            band_icon::BandIcon::Drive as i128
        ]
    );
    println!(
        "bidi_removed_by_x9\tBidiClass\t{}\t{:?}",
        name::<bidi_removed_by_x9::BidiClass>(),
        [
            bidi_removed_by_x9::BidiClass::L as i128,
            bidi_removed_by_x9::BidiClass::R as i128,
            bidi_removed_by_x9::BidiClass::AL as i128,
            bidi_removed_by_x9::BidiClass::EN as i128,
            bidi_removed_by_x9::BidiClass::ES as i128,
            bidi_removed_by_x9::BidiClass::ET as i128,
            bidi_removed_by_x9::BidiClass::AN as i128,
            bidi_removed_by_x9::BidiClass::CS as i128,
            bidi_removed_by_x9::BidiClass::NSM as i128,
            bidi_removed_by_x9::BidiClass::BN as i128,
            bidi_removed_by_x9::BidiClass::B as i128,
            bidi_removed_by_x9::BidiClass::S as i128,
            bidi_removed_by_x9::BidiClass::WS as i128,
            bidi_removed_by_x9::BidiClass::ON as i128,
            bidi_removed_by_x9::BidiClass::LRE as i128,
            bidi_removed_by_x9::BidiClass::LRO as i128,
            bidi_removed_by_x9::BidiClass::RLE as i128,
            bidi_removed_by_x9::BidiClass::RLO as i128,
            bidi_removed_by_x9::BidiClass::PDF as i128,
            bidi_removed_by_x9::BidiClass::LRI as i128,
            bidi_removed_by_x9::BidiClass::RLI as i128,
            bidi_removed_by_x9::BidiClass::FSI as i128,
            bidi_removed_by_x9::BidiClass::PDI as i128
        ]
    );
    println!(
        "bridge_decision_resolve\tBridgeDecision\t{}\t{:?}",
        name::<bridge_decision_resolve::BridgeDecision>(),
        [
            bridge_decision_resolve::BridgeDecision::Allow as i128,
            bridge_decision_resolve::BridgeDecision::Deny as i128,
            bridge_decision_resolve::BridgeDecision::Fallback as i128
        ]
    );
    println!(
        "classify_shape\tShapeVerdict\t{}\t{:?}",
        name::<classify_shape::ShapeVerdict>(),
        [
            classify_shape::ShapeVerdict::Reject as i128,
            classify_shape::ShapeVerdict::OneToOne as i128,
            classify_shape::ShapeVerdict::Collapsed as i128
        ]
    );
    println!(
        "containment_level\tContainmentMode\t{}\t{:?}",
        name::<containment_level::ContainmentMode>(),
        [
            containment_level::ContainmentMode::Containment as i128,
            containment_level::ContainmentMode::Safety as i128,
            containment_level::ContainmentMode::User as i128
        ]
    );
    println!(
        "cursor_shown\tCursorStyle\t{}\t{:?}",
        name::<cursor_shown::CursorStyle>(),
        [
            cursor_shown::CursorStyle::BlinkingBlock as i128,
            cursor_shown::CursorStyle::SteadyBlock as i128,
            cursor_shown::CursorStyle::BlinkingUnderline as i128,
            cursor_shown::CursorStyle::SteadyUnderline as i128,
            cursor_shown::CursorStyle::BlinkingBar as i128,
            cursor_shown::CursorStyle::SteadyBar as i128,
            cursor_shown::CursorStyle::Hidden as i128,
            cursor_shown::CursorStyle::HollowBlock as i128,
            cursor_shown::CursorStyle::Bolt as i128
        ]
    );
    println!(
        "dr_class_grant_stable\tDrClass\t{}\t{:?}",
        name::<dr_class_grant_stable::DrClass>(),
        [
            dr_class_grant_stable::DrClass::Identity as i128,
            dr_class_grant_stable::DrClass::Cdhash as i128,
            dr_class_grant_stable::DrClass::Unsigned as i128,
            dr_class_grant_stable::DrClass::Unknown as i128
        ]
    );
    println!(
        "family_mode\tFamily\t{}\t{:?}",
        name::<family_mode::Family>(),
        [
            family_mode::Family::Privacy as i128,
            family_mode::Family::Update as i128,
            family_mode::Family::Upgrade as i128,
            family_mode::Family::UpgradeHost as i128,
            family_mode::Family::Resume as i128,
            family_mode::Family::Supervisor as i128,
            family_mode::Family::Accounts as i128,
            family_mode::Family::Ai as i128,
            family_mode::Family::Toolchain as i128,
            family_mode::Family::Disk as i128,
            family_mode::Family::Render as i128,
            family_mode::Family::Terminal as i128,
            family_mode::Family::Removed as i128,
            family_mode::Family::ApiOutage as i128,
            family_mode::Family::LongHold as i128,
            family_mode::Family::FleetUnreadable as i128,
            family_mode::Family::HugeDir as i128,
            family_mode::Family::ServiceMemory as i128,
            family_mode::Family::FabricState as i128,
            family_mode::Family::Occupancy as i128,
            family_mode::Family::Setup as i128,
            family_mode::Family::Secrets as i128
        ]
    );
    println!(
        "family_mode\tMode\t{}\t{:?}",
        name::<family_mode::Mode>(),
        [
            family_mode::Mode::Level as i128,
            family_mode::Mode::Event as i128
        ]
    );
    println!(
        "folder_absent_means_allowed\tFolder\t{}\t{:?}",
        name::<folder_absent_means_allowed::Folder>(),
        [
            folder_absent_means_allowed::Folder::Documents as i128,
            folder_absent_means_allowed::Folder::Desktop as i128,
            folder_absent_means_allowed::Folder::Downloads as i128,
            folder_absent_means_allowed::Folder::AppData as i128
        ]
    );
    println!(
        "http_method\tMethod\t{}\t{:?}",
        name::<http_method::Method>(),
        [
            http_method::Method::Get as i128,
            http_method::Method::Head as i128,
            http_method::Method::Post as i128,
            http_method::Method::Patch as i128,
            http_method::Method::Put as i128,
            http_method::Method::Delete as i128
        ]
    );
    println!(
        "image_anchor_grant_unverifiable\tImageAnchor\t{}\t{:?}",
        name::<image_anchor_grant_unverifiable::ImageAnchor>(),
        [
            image_anchor_grant_unverifiable::ImageAnchor::Live as i128,
            image_anchor_grant_unverifiable::ImageAnchor::Displaced as i128,
            image_anchor_grant_unverifiable::ImageAnchor::Deleted as i128,
            image_anchor_grant_unverifiable::ImageAnchor::NotBundled as i128,
            image_anchor_grant_unverifiable::ImageAnchor::Unknown as i128
        ]
    );
    println!(
        "key_event_kitty_value\tKeyEventType\t{}\t{:?}",
        name::<key_event_kitty_value::KeyEventType>(),
        [
            key_event_kitty_value::KeyEventType::Press as i128,
            key_event_kitty_value::KeyEventType::Repeat as i128,
            key_event_kitty_value::KeyEventType::Release as i128
        ]
    );
    println!(
        "log_record_cap\tLevel\t{}\t{:?}",
        name::<log_record_cap::Level>(),
        [
            log_record_cap::Level::Error as i128,
            log_record_cap::Level::Warn as i128,
            log_record_cap::Level::Info as i128,
            log_record_cap::Level::Debug as i128,
            log_record_cap::Level::Trace as i128
        ]
    );
    println!(
        "mouse\tMouseButton\t{}\t{:?}",
        name::<mouse::MouseButton>(),
        [
            mouse::MouseButton::Left as i128,
            mouse::MouseButton::Middle as i128,
            mouse::MouseButton::Right as i128,
            mouse::MouseButton::Back as i128,
            mouse::MouseButton::Forward as i128
        ]
    );
    println!(
        "mouse\tWheelDir\t{}\t{:?}",
        name::<mouse::WheelDir>(),
        [
            mouse::WheelDir::Up as i128,
            mouse::WheelDir::Down as i128,
            mouse::WheelDir::Left as i128,
            mouse::WheelDir::Right as i128
        ]
    );
    println!(
        "origin_trust_rank\tOriginTag\t{}\t{:?}",
        name::<origin_trust_rank::OriginTag>(),
        [
            origin_trust_rank::OriginTag::Host as i128,
            origin_trust_rank::OriginTag::ConfigFile as i128,
            origin_trust_rank::OriginTag::User as i128,
            origin_trust_rank::OriginTag::UserTyped as i128,
            origin_trust_rank::OriginTag::Ai as i128,
            origin_trust_rank::OriginTag::PtySafe as i128,
            origin_trust_rank::OriginTag::Pty as i128,
            origin_trust_rank::OriginTag::NetworkUntrusted as i128
        ]
    );
    println!(
        "panel_column\tPanelRenderer\t{}\t{:?}",
        name::<panel_column::PanelRenderer>(),
        [
            panel_column::PanelRenderer::Fullscreen as i128,
            panel_column::PanelRenderer::Inline as i128
        ]
    );
    println!(
        "phase_program\tProgram\t{}\t{:?}",
        name::<phase_program::Program>(),
        [
            phase_program::Program::Claude as i128,
            phase_program::Program::Codex as i128,
            phase_program::Program::Agy as i128,
            phase_program::Program::Muse as i128,
            phase_program::Program::Grok as i128,
            phase_program::Program::Kimi as i128,
            phase_program::Program::Generic as i128
        ]
    );
    println!(
        "pm1_arming\tArming\t{}\t{:?}",
        name::<pm1_arming::Arming>(),
        [
            pm1_arming::Arming::App as i128,
            pm1_arming::Arming::Other as i128,
            pm1_arming::Arming::AppAfterCommit as i128,
            pm1_arming::Arming::Lab as i128
        ]
    );
    println!(
        "pm1_attempt_finish\tAttemptResult\t{}\t{:?}",
        name::<pm1_attempt_finish::AttemptResult>(),
        [
            pm1_attempt_finish::AttemptResult::Accepted as i128,
            pm1_attempt_finish::AttemptResult::InstalledNeedsRelaunch as i128,
            pm1_attempt_finish::AttemptResult::Blocked as i128,
            pm1_attempt_finish::AttemptResult::Failed as i128
        ]
    );
    println!(
        "pm1_attempt_finish\tAttemptDisposition\t{}\t{:?}",
        name::<pm1_attempt_finish::AttemptDisposition>(),
        [
            pm1_attempt_finish::AttemptDisposition::Complete as i128,
            pm1_attempt_finish::AttemptDisposition::Retry as i128,
            pm1_attempt_finish::AttemptDisposition::ManualOnly as i128
        ]
    );
    println!(
        "pm1_blink_clock_armed\tCursorStyle\t{}\t{:?}",
        name::<pm1_blink_clock_armed::CursorStyle>(),
        [
            pm1_blink_clock_armed::CursorStyle::BlinkingBlock as i128,
            pm1_blink_clock_armed::CursorStyle::SteadyBlock as i128,
            pm1_blink_clock_armed::CursorStyle::BlinkingUnderline as i128,
            pm1_blink_clock_armed::CursorStyle::SteadyUnderline as i128,
            pm1_blink_clock_armed::CursorStyle::BlinkingBar as i128,
            pm1_blink_clock_armed::CursorStyle::SteadyBar as i128,
            pm1_blink_clock_armed::CursorStyle::Hidden as i128,
            pm1_blink_clock_armed::CursorStyle::HollowBlock as i128,
            pm1_blink_clock_armed::CursorStyle::Bolt as i128
        ]
    );
    println!(
        "pm1_boot_health\tBootHealthLane\t{}\t{:?}",
        name::<pm1_boot_health::BootHealthLane>(),
        [
            pm1_boot_health::BootHealthLane::FullProof as i128,
            pm1_boot_health::BootHealthLane::CountOnly as i128
        ]
    );
    println!(
        "pm1_capture_after_present\tCaptureAfterPresentDecision\t{}\t{:?}",
        name::<pm1_capture_after_present::CaptureAfterPresentDecision>(),
        [
            pm1_capture_after_present::CaptureAfterPresentDecision::Capture as i128,
            pm1_capture_after_present::CaptureAfterPresentDecision::Retry as i128,
            pm1_capture_after_present::CaptureAfterPresentDecision::FailClosed as i128
        ]
    );
    println!(
        "pm1_carry_ceiling\tCarryCeiling\t{}\t{:?}",
        name::<pm1_carry_ceiling::CarryCeiling>(),
        [
            pm1_carry_ceiling::CarryCeiling::Full as i128,
            pm1_carry_ceiling::CarryCeiling::Visible as i128,
            pm1_carry_ceiling::CarryCeiling::Repaint as i128
        ]
    );
    println!(
        "pm1_chrome_face\tChromeFacePick\t{}\t{:?}",
        name::<pm1_chrome_face::ChromeFacePick>(),
        [
            pm1_chrome_face::ChromeFacePick::Bold as i128,
            pm1_chrome_face::ChromeFacePick::Primary as i128,
            pm1_chrome_face::ChromeFacePick::Fallback as i128
        ]
    );
    println!(
        "pm1_class_rank\tClass\t{}\t{:?}",
        name::<pm1_class_rank::Class>(),
        [
            pm1_class_rank::Class::Profanity as i128,
            pm1_class_rank::Class::Feline as i128,
            pm1_class_rank::Class::Canine as i128,
            pm1_class_rank::Class::Animal as i128,
            pm1_class_rank::Class::Emphasis as i128
        ]
    );
    println!(
        "pm1_cli_mark\tMark\t{}\t{:?}",
        name::<pm1_cli_mark::Mark>(),
        [
            pm1_cli_mark::Mark::Ok as i128,
            pm1_cli_mark::Mark::Note as i128,
            pm1_cli_mark::Mark::Warn as i128,
            pm1_cli_mark::Mark::Fail as i128
        ]
    );
    println!(
        "pm1_cli_verb\tVerb\t{}\t{:?}",
        name::<pm1_cli_verb::Verb>(),
        [
            pm1_cli_verb::Verb::Ctl as i128,
            pm1_cli_verb::Verb::Conn as i128,
            pm1_cli_verb::Verb::ResourceRun as i128,
            pm1_cli_verb::Verb::Pkg as i128,
            pm1_cli_verb::Verb::Agh as i128,
            pm1_cli_verb::Verb::Fleet as i128,
            pm1_cli_verb::Verb::Node as i128,
            pm1_cli_verb::Verb::Drive as i128,
            pm1_cli_verb::Verb::Link as i128,
            pm1_cli_verb::Verb::Fabric as i128,
            pm1_cli_verb::Verb::Ship as i128,
            pm1_cli_verb::Verb::Release as i128,
            pm1_cli_verb::Verb::Update as i128,
            pm1_cli_verb::Verb::Agents as i128,
            pm1_cli_verb::Verb::Ai as i128,
            pm1_cli_verb::Verb::Machines as i128,
            pm1_cli_verb::Verb::Init as i128,
            pm1_cli_verb::Verb::Secrets as i128,
            pm1_cli_verb::Verb::Members as i128,
            pm1_cli_verb::Verb::Db as i128,
            pm1_cli_verb::Verb::Harness as i128,
            pm1_cli_verb::Verb::Keeper as i128,
            pm1_cli_verb::Verb::Acaffiene as i128,
            pm1_cli_verb::Verb::Theme as i128,
            pm1_cli_verb::Verb::Edit as i128,
            pm1_cli_verb::Verb::NewTab as i128,
            pm1_cli_verb::Verb::NewWindow as i128,
            pm1_cli_verb::Verb::SplitPane as i128
        ]
    );
    println!(
        "pm1_completion_consent\tConsent\t{}\t{:?}",
        name::<pm1_completion_consent::Consent>(),
        [
            pm1_completion_consent::Consent::InstallingAterm as i128,
            pm1_completion_consent::Consent::Explicit as i128
        ]
    );
    println!(
        "pm1_converge_outcome\tOutcome\t{}\t{:?}",
        name::<pm1_converge_outcome::Outcome>(),
        [
            pm1_converge_outcome::Outcome::Ok as i128,
            pm1_converge_outcome::Outcome::Planned as i128,
            pm1_converge_outcome::Outcome::Changed as i128,
            pm1_converge_outcome::Outcome::Person as i128,
            pm1_converge_outcome::Outcome::Blocked as i128,
            pm1_converge_outcome::Outcome::NotApplicable as i128,
            pm1_converge_outcome::Outcome::Deferred as i128,
            pm1_converge_outcome::Outcome::Unknown as i128,
            pm1_converge_outcome::Outcome::Failed as i128
        ]
    );
    println!(
        "pm1_decide_bind\tBindAction\t{}\t{:?}",
        name::<pm1_decide_bind::BindAction>(),
        [
            pm1_decide_bind::BindAction::RemoveAndBind as i128,
            pm1_decide_bind::BindAction::RefuseLiveSocket as i128
        ]
    );
    println!(
        "pm1_drop_taint\tPresentDropReason\t{}\t{:?}",
        name::<pm1_drop_taint::PresentDropReason>(),
        [
            pm1_drop_taint::PresentDropReason::None as i128,
            pm1_drop_taint::PresentDropReason::GpuReconfigured as i128,
            pm1_drop_taint::PresentDropReason::GpuTimeout as i128,
            pm1_drop_taint::PresentDropReason::GpuUnavailable as i128,
            pm1_drop_taint::PresentDropReason::GpuOccluded as i128,
            pm1_drop_taint::PresentDropReason::GpuValidation as i128,
            pm1_drop_taint::PresentDropReason::CpuResize as i128,
            pm1_drop_taint::PresentDropReason::CpuAcquire as i128,
            pm1_drop_taint::PresentDropReason::CpuCommit as i128,
            pm1_drop_taint::PresentDropReason::TargetMismatch as i128,
            pm1_drop_taint::PresentDropReason::Virtual as i128,
            pm1_drop_taint::PresentDropReason::CpuRaster as i128
        ]
    );
    println!(
        "pm1_durable_post\tDurablePostDecision\t{}\t{:?}",
        name::<pm1_durable_post::DurablePostDecision>(),
        [
            pm1_durable_post::DurablePostDecision::ConvergeVisible as i128,
            pm1_durable_post::DurablePostDecision::PersistIntentThenPost as i128,
            pm1_durable_post::DurablePostDecision::AwaitVisibility as i128
        ]
    );
    println!(
        "pm1_held_loss\tHeldLoss\t{}\t{:?}",
        name::<pm1_held_loss::HeldLoss>(),
        [
            pm1_held_loss::HeldLoss::ScreenOnly as i128,
            pm1_held_loss::HeldLoss::Withheld as i128,
            pm1_held_loss::HeldLoss::Failed as i128
        ]
    );
    println!(
        "pm1_launch_gates\tLinuxTrialStart\t{}\t{:?}",
        name::<pm1_launch_gates::LinuxTrialStart>(),
        [
            pm1_launch_gates::LinuxTrialStart::Window as i128,
            pm1_launch_gates::LinuxTrialStart::WindowOnceOpen as i128,
            pm1_launch_gates::LinuxTrialStart::Session as i128
        ]
    );
    println!(
        "pm1_launch_gates\tResampleCause\t{}\t{:?}",
        name::<pm1_launch_gates::ResampleCause>(),
        [
            pm1_launch_gates::ResampleCause::SettingsBurst as i128,
            pm1_launch_gates::ResampleCause::Poll as i128
        ]
    );
    println!(
        "pm1_leaf_close\tLeafCloseRecordKind\t{}\t{:?}",
        name::<pm1_leaf_close::LeafCloseRecordKind>(),
        [
            pm1_leaf_close::LeafCloseRecordKind::ClosedView as i128,
            pm1_leaf_close::LeafCloseRecordKind::ClosedTab as i128
        ]
    );
    println!(
        "pm1_lights_mode\tMode\t{}\t{:?}",
        name::<pm1_lights_mode::Mode>(),
        [
            pm1_lights_mode::Mode::Bypass as i128,
            pm1_lights_mode::Mode::Auto as i128,
            pm1_lights_mode::Mode::AcceptEdits as i128,
            pm1_lights_mode::Mode::DontAsk as i128,
            pm1_lights_mode::Mode::Plan as i128,
            pm1_lights_mode::Mode::Manual as i128
        ]
    );
    println!(
        "pm1_lower_role\tSemanticRole\t{}\t{:?}",
        name::<pm1_lower_role::SemanticRole>(),
        [
            pm1_lower_role::SemanticRole::Application as i128,
            pm1_lower_role::SemanticRole::Group as i128,
            pm1_lower_role::SemanticRole::Heading as i128,
            pm1_lower_role::SemanticRole::Text as i128,
            pm1_lower_role::SemanticRole::Button as i128,
            pm1_lower_role::SemanticRole::Switch as i128,
            pm1_lower_role::SemanticRole::Slider as i128,
            pm1_lower_role::SemanticRole::TextField as i128,
            pm1_lower_role::SemanticRole::RichText as i128,
            pm1_lower_role::SemanticRole::TextViewport as i128,
            pm1_lower_role::SemanticRole::Navigation as i128,
            pm1_lower_role::SemanticRole::Status as i128,
            pm1_lower_role::SemanticRole::List as i128,
            pm1_lower_role::SemanticRole::ListBox as i128,
            pm1_lower_role::SemanticRole::ListBoxOption as i128
        ]
    );
    println!(
        "pm1_lower_role\tRole\t{}\t{:?}",
        name::<pm1_lower_role::Role>(),
        [
            pm1_lower_role::Role::Unknown as i128,
            pm1_lower_role::Role::TextRun as i128,
            pm1_lower_role::Role::Label as i128,
            pm1_lower_role::Role::Link as i128,
            pm1_lower_role::Role::MenuItem as i128,
            pm1_lower_role::Role::TextInput as i128,
            pm1_lower_role::Role::Button as i128,
            pm1_lower_role::Role::List as i128,
            pm1_lower_role::Role::Switch as i128,
            pm1_lower_role::Role::Menu as i128,
            pm1_lower_role::Role::MultilineTextInput as i128,
            pm1_lower_role::Role::SearchInput as i128,
            pm1_lower_role::Role::Alert as i128,
            pm1_lower_role::Role::AlertDialog as i128,
            pm1_lower_role::Role::Application as i128,
            pm1_lower_role::Role::Document as i128,
            pm1_lower_role::Role::Grid as i128,
            pm1_lower_role::Role::Group as i128,
            pm1_lower_role::Role::Heading as i128,
            pm1_lower_role::Role::ListBox as i128,
            pm1_lower_role::Role::ListBoxOption as i128,
            pm1_lower_role::Role::MenuItemRadio as i128,
            pm1_lower_role::Role::Meter as i128,
            pm1_lower_role::Role::Navigation as i128,
            pm1_lower_role::Role::ProgressIndicator as i128,
            pm1_lower_role::Role::Slider as i128,
            pm1_lower_role::Role::Status as i128,
            pm1_lower_role::Role::Tab as i128,
            pm1_lower_role::Role::TabList as i128,
            pm1_lower_role::Role::Window as i128,
            pm1_lower_role::Role::Terminal as i128
        ]
    );
    println!(
        "pm1_menu_requires_terminal\tMenuAction\t{}\t{:?}",
        name::<pm1_menu_requires_terminal::MenuAction>(),
        [
            pm1_menu_requires_terminal::MenuAction::About as i128,
            pm1_menu_requires_terminal::MenuAction::SoftwareUpdate as i128,
            pm1_menu_requires_terminal::MenuAction::Version as i128,
            pm1_menu_requires_terminal::MenuAction::ApplyUpdate as i128,
            pm1_menu_requires_terminal::MenuAction::Preferences as i128,
            pm1_menu_requires_terminal::MenuAction::Quit as i128,
            pm1_menu_requires_terminal::MenuAction::NewWindow as i128,
            pm1_menu_requires_terminal::MenuAction::NewTab as i128,
            pm1_menu_requires_terminal::MenuAction::OpenMarkdown as i128,
            pm1_menu_requires_terminal::MenuAction::OpenEditor as i128,
            pm1_menu_requires_terminal::MenuAction::Save as i128,
            pm1_menu_requires_terminal::MenuAction::ReopenClosedTab as i128,
            pm1_menu_requires_terminal::MenuAction::ReopenClosedView as i128,
            pm1_menu_requires_terminal::MenuAction::MoveTabToNewWindow as i128,
            pm1_menu_requires_terminal::MenuAction::MoveTabToNextWindow as i128,
            pm1_menu_requires_terminal::MenuAction::ViewSessionInNewWindow as i128,
            pm1_menu_requires_terminal::MenuAction::CloseTab as i128,
            pm1_menu_requires_terminal::MenuAction::Copy as i128,
            pm1_menu_requires_terminal::MenuAction::Paste as i128,
            pm1_menu_requires_terminal::MenuAction::SelectAll as i128,
            pm1_menu_requires_terminal::MenuAction::Find as i128,
            pm1_menu_requires_terminal::MenuAction::FindNext as i128,
            pm1_menu_requires_terminal::MenuAction::FindPrev as i128,
            pm1_menu_requires_terminal::MenuAction::ToggleFullScreen as i128,
            pm1_menu_requires_terminal::MenuAction::FontIncrease as i128,
            pm1_menu_requires_terminal::MenuAction::FontDecrease as i128,
            pm1_menu_requires_terminal::MenuAction::FontActualSize as i128,
            pm1_menu_requires_terminal::MenuAction::SplitVertical as i128,
            pm1_menu_requires_terminal::MenuAction::SplitHorizontal as i128,
            pm1_menu_requires_terminal::MenuAction::ToggleMatrixRain as i128,
            pm1_menu_requires_terminal::MenuAction::FavouriteKitty as i128,
            pm1_menu_requires_terminal::MenuAction::NextKitty as i128,
            pm1_menu_requires_terminal::MenuAction::ToggleSeriousMode as i128,
            pm1_menu_requires_terminal::MenuAction::ToggleSettings as i128,
            pm1_menu_requires_terminal::MenuAction::ToggleNeedsInWindows as i128,
            pm1_menu_requires_terminal::MenuAction::StatsBarsDeck as i128,
            pm1_menu_requires_terminal::MenuAction::StatsBarsSill as i128,
            pm1_menu_requires_terminal::MenuAction::StatsBarsOff as i128,
            pm1_menu_requires_terminal::MenuAction::DeckSizeAuto as i128,
            pm1_menu_requires_terminal::MenuAction::DeckSizeFull as i128,
            pm1_menu_requires_terminal::MenuAction::DeckSizeFolded as i128,
            pm1_menu_requires_terminal::MenuAction::ToggleStatsLens as i128,
            pm1_menu_requires_terminal::MenuAction::NetworkState as i128,
            pm1_menu_requires_terminal::MenuAction::RewindPane as i128,
            pm1_menu_requires_terminal::MenuAction::ExportPaneHistory as i128,
            pm1_menu_requires_terminal::MenuAction::ForgetPaneHistory as i128,
            pm1_menu_requires_terminal::MenuAction::ForgetAllHistory as i128,
            pm1_menu_requires_terminal::MenuAction::Packages as i128,
            pm1_menu_requires_terminal::MenuAction::Messages as i128,
            pm1_menu_requires_terminal::MenuAction::SystemState as i128,
            pm1_menu_requires_terminal::MenuAction::OpenPalette as i128,
            pm1_menu_requires_terminal::MenuAction::ChooseTheme as i128,
            pm1_menu_requires_terminal::MenuAction::BrowseThemes as i128,
            pm1_menu_requires_terminal::MenuAction::ChooseTabTheme as i128,
            pm1_menu_requires_terminal::MenuAction::ClearTabTheme as i128,
            pm1_menu_requires_terminal::MenuAction::CopySessionId as i128,
            pm1_menu_requires_terminal::MenuAction::CopyCwd as i128,
            pm1_menu_requires_terminal::MenuAction::Overview as i128,
            pm1_menu_requires_terminal::MenuAction::NextNeed as i128,
            pm1_menu_requires_terminal::MenuAction::HarnessLog as i128,
            pm1_menu_requires_terminal::MenuAction::TakeOver as i128,
            pm1_menu_requires_terminal::MenuAction::HandBack as i128,
            pm1_menu_requires_terminal::MenuAction::ReadThisMac as i128,
            pm1_menu_requires_terminal::MenuAction::ReadFleet as i128,
            pm1_menu_requires_terminal::MenuAction::SummarizeFleet as i128,
            pm1_menu_requires_terminal::MenuAction::FabricStatus as i128,
            pm1_menu_requires_terminal::MenuAction::FabricOn as i128,
            pm1_menu_requires_terminal::MenuAction::FabricOff as i128,
            pm1_menu_requires_terminal::MenuAction::FleetMachines as i128,
            pm1_menu_requires_terminal::MenuAction::RenameSession as i128,
            pm1_menu_requires_terminal::MenuAction::SetRole as i128,
            pm1_menu_requires_terminal::MenuAction::ResetTerminal as i128,
            pm1_menu_requires_terminal::MenuAction::HarnessSettings as i128,
            pm1_menu_requires_terminal::MenuAction::Minimize as i128,
            pm1_menu_requires_terminal::MenuAction::Zoom as i128,
            pm1_menu_requires_terminal::MenuAction::NextTab as i128,
            pm1_menu_requires_terminal::MenuAction::PrevTab as i128,
            pm1_menu_requires_terminal::MenuAction::Help as i128
        ]
    );
    println!(
        "pm1_menu_tag\tMenuAction\t{}\t{:?}",
        name::<pm1_menu_tag::MenuAction>(),
        [
            pm1_menu_tag::MenuAction::About as i128,
            pm1_menu_tag::MenuAction::SoftwareUpdate as i128,
            pm1_menu_tag::MenuAction::Version as i128,
            pm1_menu_tag::MenuAction::ApplyUpdate as i128,
            pm1_menu_tag::MenuAction::Preferences as i128,
            pm1_menu_tag::MenuAction::Quit as i128,
            pm1_menu_tag::MenuAction::NewWindow as i128,
            pm1_menu_tag::MenuAction::NewTab as i128,
            pm1_menu_tag::MenuAction::OpenMarkdown as i128,
            pm1_menu_tag::MenuAction::OpenEditor as i128,
            pm1_menu_tag::MenuAction::Save as i128,
            pm1_menu_tag::MenuAction::ReopenClosedTab as i128,
            pm1_menu_tag::MenuAction::ReopenClosedView as i128,
            pm1_menu_tag::MenuAction::MoveTabToNewWindow as i128,
            pm1_menu_tag::MenuAction::MoveTabToNextWindow as i128,
            pm1_menu_tag::MenuAction::ViewSessionInNewWindow as i128,
            pm1_menu_tag::MenuAction::CloseTab as i128,
            pm1_menu_tag::MenuAction::Copy as i128,
            pm1_menu_tag::MenuAction::Paste as i128,
            pm1_menu_tag::MenuAction::SelectAll as i128,
            pm1_menu_tag::MenuAction::Find as i128,
            pm1_menu_tag::MenuAction::FindNext as i128,
            pm1_menu_tag::MenuAction::FindPrev as i128,
            pm1_menu_tag::MenuAction::ToggleFullScreen as i128,
            pm1_menu_tag::MenuAction::FontIncrease as i128,
            pm1_menu_tag::MenuAction::FontDecrease as i128,
            pm1_menu_tag::MenuAction::FontActualSize as i128,
            pm1_menu_tag::MenuAction::SplitVertical as i128,
            pm1_menu_tag::MenuAction::SplitHorizontal as i128,
            pm1_menu_tag::MenuAction::ToggleMatrixRain as i128,
            pm1_menu_tag::MenuAction::FavouriteKitty as i128,
            pm1_menu_tag::MenuAction::NextKitty as i128,
            pm1_menu_tag::MenuAction::ToggleSeriousMode as i128,
            pm1_menu_tag::MenuAction::ToggleSettings as i128,
            pm1_menu_tag::MenuAction::ToggleNeedsInWindows as i128,
            pm1_menu_tag::MenuAction::StatsBarsDeck as i128,
            pm1_menu_tag::MenuAction::StatsBarsSill as i128,
            pm1_menu_tag::MenuAction::StatsBarsOff as i128,
            pm1_menu_tag::MenuAction::DeckSizeAuto as i128,
            pm1_menu_tag::MenuAction::DeckSizeFull as i128,
            pm1_menu_tag::MenuAction::DeckSizeFolded as i128,
            pm1_menu_tag::MenuAction::ToggleStatsLens as i128,
            pm1_menu_tag::MenuAction::NetworkState as i128,
            pm1_menu_tag::MenuAction::RewindPane as i128,
            pm1_menu_tag::MenuAction::ExportPaneHistory as i128,
            pm1_menu_tag::MenuAction::ForgetPaneHistory as i128,
            pm1_menu_tag::MenuAction::ForgetAllHistory as i128,
            pm1_menu_tag::MenuAction::Packages as i128,
            pm1_menu_tag::MenuAction::Messages as i128,
            pm1_menu_tag::MenuAction::SystemState as i128,
            pm1_menu_tag::MenuAction::OpenPalette as i128,
            pm1_menu_tag::MenuAction::ChooseTheme as i128,
            pm1_menu_tag::MenuAction::BrowseThemes as i128,
            pm1_menu_tag::MenuAction::ChooseTabTheme as i128,
            pm1_menu_tag::MenuAction::ClearTabTheme as i128,
            pm1_menu_tag::MenuAction::CopySessionId as i128,
            pm1_menu_tag::MenuAction::CopyCwd as i128,
            pm1_menu_tag::MenuAction::Overview as i128,
            pm1_menu_tag::MenuAction::NextNeed as i128,
            pm1_menu_tag::MenuAction::HarnessLog as i128,
            pm1_menu_tag::MenuAction::TakeOver as i128,
            pm1_menu_tag::MenuAction::HandBack as i128,
            pm1_menu_tag::MenuAction::ReadThisMac as i128,
            pm1_menu_tag::MenuAction::ReadFleet as i128,
            pm1_menu_tag::MenuAction::SummarizeFleet as i128,
            pm1_menu_tag::MenuAction::FabricStatus as i128,
            pm1_menu_tag::MenuAction::FabricOn as i128,
            pm1_menu_tag::MenuAction::FabricOff as i128,
            pm1_menu_tag::MenuAction::FleetMachines as i128,
            pm1_menu_tag::MenuAction::RenameSession as i128,
            pm1_menu_tag::MenuAction::SetRole as i128,
            pm1_menu_tag::MenuAction::ResetTerminal as i128,
            pm1_menu_tag::MenuAction::HarnessSettings as i128,
            pm1_menu_tag::MenuAction::Minimize as i128,
            pm1_menu_tag::MenuAction::Zoom as i128,
            pm1_menu_tag::MenuAction::NextTab as i128,
            pm1_menu_tag::MenuAction::PrevTab as i128,
            pm1_menu_tag::MenuAction::Help as i128
        ]
    );
    println!(
        "pm1_menu_tag_inverse\tMenuAction\t{}\t{:?}",
        name::<pm1_menu_tag_inverse::MenuAction>(),
        [
            pm1_menu_tag_inverse::MenuAction::About as i128,
            pm1_menu_tag_inverse::MenuAction::SoftwareUpdate as i128,
            pm1_menu_tag_inverse::MenuAction::Version as i128,
            pm1_menu_tag_inverse::MenuAction::ApplyUpdate as i128,
            pm1_menu_tag_inverse::MenuAction::Preferences as i128,
            pm1_menu_tag_inverse::MenuAction::Quit as i128,
            pm1_menu_tag_inverse::MenuAction::NewWindow as i128,
            pm1_menu_tag_inverse::MenuAction::NewTab as i128,
            pm1_menu_tag_inverse::MenuAction::OpenMarkdown as i128,
            pm1_menu_tag_inverse::MenuAction::OpenEditor as i128,
            pm1_menu_tag_inverse::MenuAction::Save as i128,
            pm1_menu_tag_inverse::MenuAction::ReopenClosedTab as i128,
            pm1_menu_tag_inverse::MenuAction::ReopenClosedView as i128,
            pm1_menu_tag_inverse::MenuAction::MoveTabToNewWindow as i128,
            pm1_menu_tag_inverse::MenuAction::MoveTabToNextWindow as i128,
            pm1_menu_tag_inverse::MenuAction::ViewSessionInNewWindow as i128,
            pm1_menu_tag_inverse::MenuAction::CloseTab as i128,
            pm1_menu_tag_inverse::MenuAction::Copy as i128,
            pm1_menu_tag_inverse::MenuAction::Paste as i128,
            pm1_menu_tag_inverse::MenuAction::SelectAll as i128,
            pm1_menu_tag_inverse::MenuAction::Find as i128,
            pm1_menu_tag_inverse::MenuAction::FindNext as i128,
            pm1_menu_tag_inverse::MenuAction::FindPrev as i128,
            pm1_menu_tag_inverse::MenuAction::ToggleFullScreen as i128,
            pm1_menu_tag_inverse::MenuAction::FontIncrease as i128,
            pm1_menu_tag_inverse::MenuAction::FontDecrease as i128,
            pm1_menu_tag_inverse::MenuAction::FontActualSize as i128,
            pm1_menu_tag_inverse::MenuAction::SplitVertical as i128,
            pm1_menu_tag_inverse::MenuAction::SplitHorizontal as i128,
            pm1_menu_tag_inverse::MenuAction::ToggleMatrixRain as i128,
            pm1_menu_tag_inverse::MenuAction::FavouriteKitty as i128,
            pm1_menu_tag_inverse::MenuAction::NextKitty as i128,
            pm1_menu_tag_inverse::MenuAction::ToggleSeriousMode as i128,
            pm1_menu_tag_inverse::MenuAction::ToggleSettings as i128,
            pm1_menu_tag_inverse::MenuAction::ToggleNeedsInWindows as i128,
            pm1_menu_tag_inverse::MenuAction::StatsBarsDeck as i128,
            pm1_menu_tag_inverse::MenuAction::StatsBarsSill as i128,
            pm1_menu_tag_inverse::MenuAction::StatsBarsOff as i128,
            pm1_menu_tag_inverse::MenuAction::DeckSizeAuto as i128,
            pm1_menu_tag_inverse::MenuAction::DeckSizeFull as i128,
            pm1_menu_tag_inverse::MenuAction::DeckSizeFolded as i128,
            pm1_menu_tag_inverse::MenuAction::ToggleStatsLens as i128,
            pm1_menu_tag_inverse::MenuAction::NetworkState as i128,
            pm1_menu_tag_inverse::MenuAction::RewindPane as i128,
            pm1_menu_tag_inverse::MenuAction::ExportPaneHistory as i128,
            pm1_menu_tag_inverse::MenuAction::ForgetPaneHistory as i128,
            pm1_menu_tag_inverse::MenuAction::ForgetAllHistory as i128,
            pm1_menu_tag_inverse::MenuAction::Packages as i128,
            pm1_menu_tag_inverse::MenuAction::Messages as i128,
            pm1_menu_tag_inverse::MenuAction::SystemState as i128,
            pm1_menu_tag_inverse::MenuAction::OpenPalette as i128,
            pm1_menu_tag_inverse::MenuAction::ChooseTheme as i128,
            pm1_menu_tag_inverse::MenuAction::BrowseThemes as i128,
            pm1_menu_tag_inverse::MenuAction::ChooseTabTheme as i128,
            pm1_menu_tag_inverse::MenuAction::ClearTabTheme as i128,
            pm1_menu_tag_inverse::MenuAction::CopySessionId as i128,
            pm1_menu_tag_inverse::MenuAction::CopyCwd as i128,
            pm1_menu_tag_inverse::MenuAction::Overview as i128,
            pm1_menu_tag_inverse::MenuAction::NextNeed as i128,
            pm1_menu_tag_inverse::MenuAction::HarnessLog as i128,
            pm1_menu_tag_inverse::MenuAction::TakeOver as i128,
            pm1_menu_tag_inverse::MenuAction::HandBack as i128,
            pm1_menu_tag_inverse::MenuAction::ReadThisMac as i128,
            pm1_menu_tag_inverse::MenuAction::ReadFleet as i128,
            pm1_menu_tag_inverse::MenuAction::SummarizeFleet as i128,
            pm1_menu_tag_inverse::MenuAction::FabricStatus as i128,
            pm1_menu_tag_inverse::MenuAction::FabricOn as i128,
            pm1_menu_tag_inverse::MenuAction::FabricOff as i128,
            pm1_menu_tag_inverse::MenuAction::FleetMachines as i128,
            pm1_menu_tag_inverse::MenuAction::RenameSession as i128,
            pm1_menu_tag_inverse::MenuAction::SetRole as i128,
            pm1_menu_tag_inverse::MenuAction::ResetTerminal as i128,
            pm1_menu_tag_inverse::MenuAction::HarnessSettings as i128,
            pm1_menu_tag_inverse::MenuAction::Minimize as i128,
            pm1_menu_tag_inverse::MenuAction::Zoom as i128,
            pm1_menu_tag_inverse::MenuAction::NextTab as i128,
            pm1_menu_tag_inverse::MenuAction::PrevTab as i128,
            pm1_menu_tag_inverse::MenuAction::Help as i128
        ]
    );
    println!(
        "pm1_native_control\tNativeControlPrincipal\t{}\t{:?}",
        name::<pm1_native_control::NativeControlPrincipal>(),
        [
            pm1_native_control::NativeControlPrincipal::Owner as i128,
            pm1_native_control::NativeControlPrincipal::Edge as i128
        ]
    );
    println!(
        "pm1_native_control\tNativeControlTarget\t{}\t{:?}",
        name::<pm1_native_control::NativeControlTarget>(),
        [
            pm1_native_control::NativeControlTarget::App as i128,
            pm1_native_control::NativeControlTarget::BareSession as i128,
            pm1_native_control::NativeControlTarget::ExplicitSession as i128
        ]
    );
    println!(
        "pm1_native_control\tNativeControlDecision\t{}\t{:?}",
        name::<pm1_native_control::NativeControlDecision>(),
        [
            pm1_native_control::NativeControlDecision::WithoutSession as i128,
            pm1_native_control::NativeControlDecision::ResolveSession as i128,
            pm1_native_control::NativeControlDecision::Denied as i128,
            pm1_native_control::NativeControlDecision::NoActiveTerminal as i128,
            pm1_native_control::NativeControlDecision::NoSuchSession as i128
        ]
    );
    println!(
        "pm1_pending_wait\tWaitStep\t{}\t{:?}",
        name::<pm1_pending_wait::WaitStep>(),
        [
            pm1_pending_wait::WaitStep::Run as i128,
            pm1_pending_wait::WaitStep::Fail as i128,
            pm1_pending_wait::WaitStep::Wait as i128
        ]
    );
    println!(
        "pm1_restore_pass\tRestorePassSite\t{}\t{:?}",
        name::<pm1_restore_pass::RestorePassSite>(),
        [
            pm1_restore_pass::RestorePassSite::FirstAttach as i128,
            pm1_restore_pass::RestorePassSite::Park as i128
        ]
    );
    println!(
        "pm1_roster_duty\tRosterDuty\t{}\t{:?}",
        name::<pm1_roster_duty::RosterDuty>(),
        [
            pm1_roster_duty::RosterDuty::Sign as i128,
            pm1_roster_duty::RosterDuty::Finish as i128
        ]
    );
    println!(
        "pm1_row_state\tRowState\t{}\t{:?}",
        name::<pm1_row_state::RowState>(),
        [
            pm1_row_state::RowState::Published as i128,
            pm1_row_state::RowState::Staged as i128,
            pm1_row_state::RowState::Blocked as i128,
            pm1_row_state::RowState::Absent as i128,
            pm1_row_state::RowState::Skipped as i128
        ]
    );
    println!(
        "pm1_seamless\tRefusedIntakeLeave\t{}\t{:?}",
        name::<pm1_seamless::RefusedIntakeLeave>(),
        [
            pm1_seamless::RefusedIntakeLeave::Ordinary as i128,
            pm1_seamless::RefusedIntakeLeave::Passing as i128,
            pm1_seamless::RefusedIntakeLeave::ParentEndsIt as i128
        ]
    );
    println!(
        "pm1_status_words\tStatusWords\t{}\t{:?}",
        name::<pm1_status_words::StatusWords>(),
        [
            pm1_status_words::StatusWords::Current as i128,
            pm1_status_words::StatusWords::PreHangup as i128
        ]
    );
    println!(
        "pm1_wake_owner\tDeadlineOwner\t{}\t{:?}",
        name::<pm1_wake_owner::DeadlineOwner>(),
        [
            pm1_wake_owner::DeadlineOwner::None as i128,
            pm1_wake_owner::DeadlineOwner::BootHealth as i128,
            pm1_wake_owner::DeadlineOwner::PendingReveal as i128,
            pm1_wake_owner::DeadlineOwner::Blink as i128,
            pm1_wake_owner::DeadlineOwner::BellFlash as i128,
            pm1_wake_owner::DeadlineOwner::SyncHold as i128,
            pm1_wake_owner::DeadlineOwner::Autoscroll as i128,
            pm1_wake_owner::DeadlineOwner::ResizeSettle as i128,
            pm1_wake_owner::DeadlineOwner::PresentRetry as i128,
            pm1_wake_owner::DeadlineOwner::FrameCap as i128,
            pm1_wake_owner::DeadlineOwner::CursorEffect as i128,
            pm1_wake_owner::DeadlineOwner::Rain as i128,
            pm1_wake_owner::DeadlineOwner::NativePreview as i128,
            pm1_wake_owner::DeadlineOwner::Predictor as i128,
            pm1_wake_owner::DeadlineOwner::ScrollGlide as i128,
            pm1_wake_owner::DeadlineOwner::Overscroll as i128,
            pm1_wake_owner::DeadlineOwner::ScrollPill as i128,
            pm1_wake_owner::DeadlineOwner::WordDecorations as i128,
            pm1_wake_owner::DeadlineOwner::LevelUp as i128,
            pm1_wake_owner::DeadlineOwner::AutoApply as i128,
            pm1_wake_owner::DeadlineOwner::ReaderResume as i128,
            pm1_wake_owner::DeadlineOwner::UpgradeRealized as i128,
            pm1_wake_owner::DeadlineOwner::WakeHeal as i128,
            pm1_wake_owner::DeadlineOwner::Video as i128,
            pm1_wake_owner::DeadlineOwner::SessionChrome as i128,
            pm1_wake_owner::DeadlineOwner::TitleDrift as i128,
            pm1_wake_owner::DeadlineOwner::KittyTenure as i128,
            pm1_wake_owner::DeadlineOwner::MessageBand as i128,
            pm1_wake_owner::DeadlineOwner::SessionStatus as i128,
            pm1_wake_owner::DeadlineOwner::ConsentCard as i128,
            pm1_wake_owner::DeadlineOwner::Presence as i128,
            pm1_wake_owner::DeadlineOwner::HandoffPark as i128,
            pm1_wake_owner::DeadlineOwner::MessageBandMotion as i128,
            pm1_wake_owner::DeadlineOwner::SessionWaits as i128,
            pm1_wake_owner::DeadlineOwner::AosEchoHold as i128,
            pm1_wake_owner::DeadlineOwner::InputWatch as i128,
            pm1_wake_owner::DeadlineOwner::CrashJournal as i128,
            pm1_wake_owner::DeadlineOwner::UpdateChecker as i128,
            pm1_wake_owner::DeadlineOwner::SplitRegridHold as i128,
            pm1_wake_owner::DeadlineOwner::KittyAnimation as i128,
            pm1_wake_owner::DeadlineOwner::RenderEpoch as i128,
            pm1_wake_owner::DeadlineOwner::DebuggerChange as i128,
            pm1_wake_owner::DeadlineOwner::DevToolsHandOver as i128,
            pm1_wake_owner::DeadlineOwner::ClaudeCard as i128,
            pm1_wake_owner::DeadlineOwner::ThemePreview as i128,
            pm1_wake_owner::DeadlineOwner::OverviewFabric as i128,
            pm1_wake_owner::DeadlineOwner::SessionLog as i128,
            pm1_wake_owner::DeadlineOwner::HarnessActs as i128,
            pm1_wake_owner::DeadlineOwner::AutopilotTimer as i128,
            pm1_wake_owner::DeadlineOwner::ConsentObserver as i128,
            pm1_wake_owner::DeadlineOwner::Spare as i128,
            pm1_wake_owner::DeadlineOwner::OutputCadence as i128,
            pm1_wake_owner::DeadlineOwner::SystemVitals as i128,
            pm1_wake_owner::DeadlineOwner::StatsLens as i128,
            pm1_wake_owner::DeadlineOwner::AgentsPanel as i128,
            pm1_wake_owner::DeadlineOwner::StatsLive as i128,
            pm1_wake_owner::DeadlineOwner::StatsNeedle as i128,
            pm1_wake_owner::DeadlineOwner::NativeMotion as i128
        ]
    );
    println!(
        "pm1_wake_owner\tEventWakeKind\t{}\t{:?}",
        name::<pm1_wake_owner::EventWakeKind>(),
        [
            pm1_wake_owner::EventWakeKind::None as i128,
            pm1_wake_owner::EventWakeKind::Init as i128,
            pm1_wake_owner::EventWakeKind::Poll as i128,
            pm1_wake_owner::EventWakeKind::Timer as i128,
            pm1_wake_owner::EventWakeKind::WaitCancelled as i128
        ]
    );
    println!(
        "pm1_wake_owner_timer\tDeadlineOwner\t{}\t{:?}",
        name::<pm1_wake_owner_timer::DeadlineOwner>(),
        [
            pm1_wake_owner_timer::DeadlineOwner::None as i128,
            pm1_wake_owner_timer::DeadlineOwner::BootHealth as i128,
            pm1_wake_owner_timer::DeadlineOwner::PendingReveal as i128,
            pm1_wake_owner_timer::DeadlineOwner::Blink as i128,
            pm1_wake_owner_timer::DeadlineOwner::BellFlash as i128,
            pm1_wake_owner_timer::DeadlineOwner::SyncHold as i128,
            pm1_wake_owner_timer::DeadlineOwner::Autoscroll as i128,
            pm1_wake_owner_timer::DeadlineOwner::ResizeSettle as i128,
            pm1_wake_owner_timer::DeadlineOwner::PresentRetry as i128,
            pm1_wake_owner_timer::DeadlineOwner::FrameCap as i128,
            pm1_wake_owner_timer::DeadlineOwner::CursorEffect as i128,
            pm1_wake_owner_timer::DeadlineOwner::Rain as i128,
            pm1_wake_owner_timer::DeadlineOwner::NativePreview as i128,
            pm1_wake_owner_timer::DeadlineOwner::Predictor as i128,
            pm1_wake_owner_timer::DeadlineOwner::ScrollGlide as i128,
            pm1_wake_owner_timer::DeadlineOwner::Overscroll as i128,
            pm1_wake_owner_timer::DeadlineOwner::ScrollPill as i128,
            pm1_wake_owner_timer::DeadlineOwner::WordDecorations as i128,
            pm1_wake_owner_timer::DeadlineOwner::LevelUp as i128,
            pm1_wake_owner_timer::DeadlineOwner::AutoApply as i128,
            pm1_wake_owner_timer::DeadlineOwner::ReaderResume as i128,
            pm1_wake_owner_timer::DeadlineOwner::UpgradeRealized as i128,
            pm1_wake_owner_timer::DeadlineOwner::WakeHeal as i128,
            pm1_wake_owner_timer::DeadlineOwner::Video as i128,
            pm1_wake_owner_timer::DeadlineOwner::SessionChrome as i128,
            pm1_wake_owner_timer::DeadlineOwner::TitleDrift as i128,
            pm1_wake_owner_timer::DeadlineOwner::KittyTenure as i128,
            pm1_wake_owner_timer::DeadlineOwner::MessageBand as i128,
            pm1_wake_owner_timer::DeadlineOwner::SessionStatus as i128,
            pm1_wake_owner_timer::DeadlineOwner::ConsentCard as i128,
            pm1_wake_owner_timer::DeadlineOwner::Presence as i128,
            pm1_wake_owner_timer::DeadlineOwner::HandoffPark as i128,
            pm1_wake_owner_timer::DeadlineOwner::MessageBandMotion as i128,
            pm1_wake_owner_timer::DeadlineOwner::SessionWaits as i128,
            pm1_wake_owner_timer::DeadlineOwner::AosEchoHold as i128,
            pm1_wake_owner_timer::DeadlineOwner::InputWatch as i128,
            pm1_wake_owner_timer::DeadlineOwner::CrashJournal as i128,
            pm1_wake_owner_timer::DeadlineOwner::UpdateChecker as i128,
            pm1_wake_owner_timer::DeadlineOwner::SplitRegridHold as i128,
            pm1_wake_owner_timer::DeadlineOwner::KittyAnimation as i128,
            pm1_wake_owner_timer::DeadlineOwner::RenderEpoch as i128,
            pm1_wake_owner_timer::DeadlineOwner::DebuggerChange as i128,
            pm1_wake_owner_timer::DeadlineOwner::DevToolsHandOver as i128,
            pm1_wake_owner_timer::DeadlineOwner::ClaudeCard as i128,
            pm1_wake_owner_timer::DeadlineOwner::ThemePreview as i128,
            pm1_wake_owner_timer::DeadlineOwner::OverviewFabric as i128,
            pm1_wake_owner_timer::DeadlineOwner::SessionLog as i128,
            pm1_wake_owner_timer::DeadlineOwner::HarnessActs as i128,
            pm1_wake_owner_timer::DeadlineOwner::AutopilotTimer as i128,
            pm1_wake_owner_timer::DeadlineOwner::ConsentObserver as i128,
            pm1_wake_owner_timer::DeadlineOwner::Spare as i128,
            pm1_wake_owner_timer::DeadlineOwner::OutputCadence as i128,
            pm1_wake_owner_timer::DeadlineOwner::SystemVitals as i128,
            pm1_wake_owner_timer::DeadlineOwner::StatsLens as i128,
            pm1_wake_owner_timer::DeadlineOwner::AgentsPanel as i128,
            pm1_wake_owner_timer::DeadlineOwner::StatsLive as i128,
            pm1_wake_owner_timer::DeadlineOwner::StatsNeedle as i128,
            pm1_wake_owner_timer::DeadlineOwner::NativeMotion as i128
        ]
    );
    println!(
        "pm1_wake_owner_timer\tEventWakeKind\t{}\t{:?}",
        name::<pm1_wake_owner_timer::EventWakeKind>(),
        [
            pm1_wake_owner_timer::EventWakeKind::None as i128,
            pm1_wake_owner_timer::EventWakeKind::Init as i128,
            pm1_wake_owner_timer::EventWakeKind::Poll as i128,
            pm1_wake_owner_timer::EventWakeKind::Timer as i128,
            pm1_wake_owner_timer::EventWakeKind::WaitCancelled as i128
        ]
    );
    println!(
        "pm1_watchdog\tBreadcrumb\t{}\t{:?}",
        name::<pm1_watchdog::Breadcrumb>(),
        [
            pm1_watchdog::Breadcrumb::Startup as i128,
            pm1_watchdog::Breadcrumb::AboutToWait as i128,
            pm1_watchdog::Breadcrumb::WindowEvent as i128,
            pm1_watchdog::Breadcrumb::UserEvent as i128,
            pm1_watchdog::Breadcrumb::NewEvents as i128,
            pm1_watchdog::Breadcrumb::ResizeSettle as i128,
            pm1_watchdog::Breadcrumb::UpdateHandoff as i128,
            pm1_watchdog::Breadcrumb::Modal as i128,
            pm1_watchdog::Breadcrumb::AboutToWaitWork as i128,
            pm1_watchdog::Breadcrumb::ShutdownWait as i128
        ]
    );
    println!(
        "pm1_watchdog\tPhase\t{}\t{:?}",
        name::<pm1_watchdog::Phase>(),
        [
            pm1_watchdog::Phase::None as i128,
            pm1_watchdog::Phase::PixelBackendRedeem as i128,
            pm1_watchdog::Phase::ImageCapture as i128
        ]
    );
    println!(
        "pm1_wheel_route\tWheelRoute\t{}\t{:?}",
        name::<pm1_wheel_route::WheelRoute>(),
        [
            pm1_wheel_route::WheelRoute::Report as i128,
            pm1_wheel_route::WheelRoute::AltScroll as i128,
            pm1_wheel_route::WheelRoute::Viewport as i128
        ]
    );
    println!(
        "pm1_window_title\tWindowTitleAuthority\t{}\t{:?}",
        name::<pm1_window_title::WindowTitleAuthority>(),
        [
            pm1_window_title::WindowTitleAuthority::Search as i128,
            pm1_window_title::WindowTitleAuthority::Canonical as i128
        ]
    );
    println!(
        "presence_due_now\tDue\t{}\t{:?}",
        name::<presence_due_now::Due>(),
        [
            presence_due_now::Due::First as i128,
            presence_due_now::Due::Changed as i128,
            presence_due_now::Due::Unchanged as i128,
            presence_due_now::Due::Capped as i128
        ]
    );
    println!(
        "qos_clamped\tQos\t{}\t{:?}",
        name::<qos_clamped::Qos>(),
        [
            qos_clamped::Qos::UserInteractive as i128,
            qos_clamped::Qos::UserInitiated as i128,
            qos_clamped::Qos::Default as i128,
            qos_clamped::Qos::Utility as i128,
            qos_clamped::Qos::Background as i128,
            qos_clamped::Qos::Unspecified as i128
        ]
    );
    println!(
        "reset_kind_takeable\tResetKind\t{}\t{:?}",
        name::<reset_kind_takeable::ResetKind>(),
        [
            reset_kind_takeable::ResetKind::Session as i128,
            reset_kind_takeable::ResetKind::Weekly as i128,
            reset_kind_takeable::ResetKind::Fable as i128,
            reset_kind_takeable::ResetKind::Full as i128
        ]
    );
    println!(
        "reset_offer_shows_button\tResetOffer\t{}\t{:?}",
        name::<reset_offer_shows_button::ResetOffer>(),
        [
            reset_offer_shows_button::ResetOffer::Offer as i128,
            reset_offer_shows_button::ResetOffer::ExplainRebuild as i128,
            reset_offer_shows_button::ResetOffer::HideNoTool as i128,
            reset_offer_shows_button::ResetOffer::HideNoBundleId as i128
        ]
    );
    println!(
        "role_standing\tRole\t{}\t{:?}",
        name::<role_standing::Role>(),
        [
            role_standing::Role::Once as i128,
            role_standing::Role::Session as i128,
            role_standing::Role::Persist as i128,
            role_standing::Role::ModeSwitch as i128,
            role_standing::Role::Deny as i128,
            role_standing::Role::Exit as i128,
            role_standing::Role::Trust as i128,
            role_standing::Role::AutoResume as i128,
            role_standing::Role::Answer as i128,
            role_standing::Role::Other as i128
        ]
    );
    println!(
        "screen_buffer_from_bool\tScreenBuffer\t{}\t{:?}",
        name::<screen_buffer_from_bool::ScreenBuffer>(),
        [
            screen_buffer_from_bool::ScreenBuffer::Main as i128,
            screen_buffer_from_bool::ScreenBuffer::Alternate as i128
        ]
    );
    println!(
        "select_face\tFaceId\t{}\t{:?}",
        name::<select_face::FaceId>(),
        [
            select_face::FaceId::Primary as i128,
            select_face::FaceId::BoldPrimary as i128,
            select_face::FaceId::Fallback as i128,
            select_face::FaceId::SymbolFallback as i128,
            select_face::FaceId::Procedural as i128,
            select_face::FaceId::ColorEmoji as i128,
            select_face::FaceId::ColorEmojiMono as i128,
            select_face::FaceId::DisplayMix as i128,
            select_face::FaceId::RuntimeFallback as i128
        ]
    );
    println!(
        "tccutil\tTccutilPresence\t{}\t{:?}",
        name::<tccutil::TccutilPresence>(),
        [
            tccutil::TccutilPresence::Executable as i128,
            tccutil::TccutilPresence::Missing as i128,
            tccutil::TccutilPresence::NotExecutable as i128,
            tccutil::TccutilPresence::Unknown as i128
        ]
    );
    println!(
        "uri_scheme_default_port\tScheme\t{}\t{:?}",
        name::<uri_scheme_default_port::Scheme>(),
        [
            uri_scheme_default_port::Scheme::Http as i128,
            uri_scheme_default_port::Scheme::Https as i128
        ]
    );
    println!(
        "vt_decscl_param\tVtLevel\t{}\t{:?}",
        name::<vt_decscl_param::VtLevel>(),
        [
            vt_decscl_param::VtLevel::VT100 as i128,
            vt_decscl_param::VtLevel::VT220 as i128,
            vt_decscl_param::VtLevel::VT240 as i128,
            vt_decscl_param::VtLevel::VT320 as i128,
            vt_decscl_param::VtLevel::VT330 as i128,
            vt_decscl_param::VtLevel::VT340 as i128,
            vt_decscl_param::VtLevel::VT420 as i128,
            vt_decscl_param::VtLevel::VT510 as i128,
            vt_decscl_param::VtLevel::VT520 as i128,
            vt_decscl_param::VtLevel::VT525 as i128
        ]
    );
    println!(
        "wait_end_echo\tWaitEnd\t{}\t{:?}",
        name::<wait_end_echo::WaitEnd>(),
        [
            wait_end_echo::WaitEnd::Done as i128,
            wait_end_echo::WaitEnd::Stopped as i128,
            wait_end_echo::WaitEnd::Gone as i128,
            wait_end_echo::WaitEnd::Failed as i128
        ]
    );
    println!(
        "wait_end_echo\tEchoKind\t{}\t{:?}",
        name::<wait_end_echo::EchoKind>(),
        [
            wait_end_echo::EchoKind::Complete as i128,
            wait_end_echo::EchoKind::Fault as i128,
            wait_end_echo::EchoKind::Vanish as i128
        ]
    );
    println!(
        "waiter\tWaiter\t{}\t{:?}",
        name::<waiter::Waiter>(),
        [
            waiter::Waiter::Person as i128,
            waiter::Waiter::Nobody as i128
        ]
    );
    println!(
        "watermark\tWatermarkLevel\t{}\t{:?}",
        name::<watermark::WatermarkLevel>(),
        [
            watermark::WatermarkLevel::Green as i128,
            watermark::WatermarkLevel::Yellow as i128,
            watermark::WatermarkLevel::Red as i128
        ]
    );
    println!(
        "wire_kind_carries_fd\tKind\t{}\t{:?}",
        name::<wire_kind_carries_fd::Kind>(),
        [
            wire_kind_carries_fd::Kind::Hello as i128,
            wire_kind_carries_fd::Kind::Welcome as i128,
            wire_kind_carries_fd::Kind::Register as i128,
            wire_kind_carries_fd::Kind::Meta as i128,
            wire_kind_carries_fd::Kind::Release as i128,
            wire_kind_carries_fd::Kind::Pending as i128,
            wire_kind_carries_fd::Kind::Bye as i128,
            wire_kind_carries_fd::Kind::Offer as i128,
            wire_kind_carries_fd::Kind::Orphans as i128,
            wire_kind_carries_fd::Kind::Status as i128,
            wire_kind_carries_fd::Kind::RestartWhenSafe as i128,
            wire_kind_carries_fd::Kind::Adopt as i128,
            wire_kind_carries_fd::Kind::Refused as i128,
            wire_kind_carries_fd::Kind::Companion as i128,
            wire_kind_carries_fd::Kind::CompanionOffer as i128,
            wire_kind_carries_fd::Kind::CompanionRelease as i128,
            wire_kind_carries_fd::Kind::Sync as i128
        ]
    );
    println!(
        "bv_creation_flags\tConsole\t{}\t{:?}",
        name::<bv_creation_flags::Console>(),
        [
            bv_creation_flags::Console::Quiet as i128,
            bv_creation_flags::Console::Detached as i128
        ]
    );
}
