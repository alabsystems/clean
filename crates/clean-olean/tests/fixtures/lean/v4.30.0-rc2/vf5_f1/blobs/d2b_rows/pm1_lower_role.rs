#![allow(dead_code)]
// D-2(b) rows behind PM-1 (Clean docs/DECISIONS.md R215): see `pm1_cli_mark.rs`.

// aterm: crates/aterm-gui/src/native_ui.rs `SemanticRole`, crates/aterm-a11y/src/model/mod.rs
// `Role` (derives and `#[default]` dropped; the plan's "third-party accesskit::Role" is
// aterm-a11y's own `Role` now), crates/aterm-gui/src/native_accessibility.rs `lower_role` (its
// module is `cfg(a11y_tree)`, set on this triple)
pub enum SemanticRole {
    Application,
    Group,
    Heading,
    Text,
    Button,
    Switch,
    Slider,
    TextField,
    RichText,
    TextViewport,
    Navigation,
    Status,
    List,
    ListBox,
    ListBoxOption,
}
pub enum Role {
    Unknown,
    TextRun,
    Label,
    Link,
    MenuItem,
    TextInput,
    Button,
    List,
    Switch,
    Menu,
    MultilineTextInput,
    SearchInput,
    Alert,
    AlertDialog,
    Application,
    Document,
    Grid,
    Group,
    Heading,
    ListBox,
    ListBoxOption,
    MenuItemRadio,
    Meter,
    Navigation,
    ProgressIndicator,
    Slider,
    Status,
    Tab,
    TabList,
    Window,
    Terminal,
}
pub const fn lower_role(role: SemanticRole) -> Role {
    match role {
        SemanticRole::Application => Role::Application,
        SemanticRole::Group => Role::Group,
        SemanticRole::Heading => Role::Heading,
        SemanticRole::Text => Role::Label,
        SemanticRole::Button => Role::Button,
        SemanticRole::Switch => Role::Switch,
        SemanticRole::Slider => Role::Slider,
        SemanticRole::TextField => Role::TextInput,
        SemanticRole::RichText => Role::Document,
        SemanticRole::TextViewport => Role::MultilineTextInput,
        SemanticRole::Navigation => Role::Navigation,
        SemanticRole::Status => Role::Status,
        SemanticRole::List => Role::List,
        SemanticRole::ListBox => Role::ListBox,
        SemanticRole::ListBoxOption => Role::ListBoxOption,
    }
}
/// aterm-gui SPECS.md a11y-role-table: lower_role is the total map Application->Application,
/// Group->Group, Heading->Heading, Text->Label, Button->Button, Switch->Switch, Slider->Slider,
/// TextField->TextInput, RichText->Document, TextViewport->MultilineTextInput,
/// Navigation->Navigation, Status->Status, List->List, ListBox->ListBox,
/// ListBoxOption->ListBoxOption (compared by tag).
pub fn lower_role_spec(role: SemanticRole) -> u8 {
    let result = match role {
        SemanticRole::Application => Role::Application,
        SemanticRole::Group => Role::Group,
        SemanticRole::Heading => Role::Heading,
        SemanticRole::Text => Role::Label,
        SemanticRole::Button => Role::Button,
        SemanticRole::Switch => Role::Switch,
        SemanticRole::Slider => Role::Slider,
        SemanticRole::TextField => Role::TextInput,
        SemanticRole::RichText => Role::Document,
        SemanticRole::TextViewport => Role::MultilineTextInput,
        SemanticRole::Navigation => Role::Navigation,
        SemanticRole::Status => Role::Status,
        SemanticRole::List => Role::List,
        SemanticRole::ListBox => Role::ListBox,
        SemanticRole::ListBoxOption => Role::ListBoxOption,
    };
    let ok = {
        let want = match role {
            SemanticRole::Application => Role::Application,
            SemanticRole::Group => Role::Group,
            SemanticRole::Heading => Role::Heading,
            SemanticRole::Text => Role::Label,
            SemanticRole::Button => Role::Button,
            SemanticRole::Switch => Role::Switch,
            SemanticRole::Slider => Role::Slider,
            SemanticRole::TextField => Role::TextInput,
            SemanticRole::RichText => Role::Document,
            SemanticRole::TextViewport => Role::MultilineTextInput,
            SemanticRole::Navigation => Role::Navigation,
            SemanticRole::Status => Role::Status,
            SemanticRole::List => Role::List,
            SemanticRole::ListBox => Role::ListBox,
            SemanticRole::ListBoxOption => Role::ListBoxOption,
        };
        result as u8 == want as u8
    };
    let z = ok as u8;
    z - 1 + 1
}
