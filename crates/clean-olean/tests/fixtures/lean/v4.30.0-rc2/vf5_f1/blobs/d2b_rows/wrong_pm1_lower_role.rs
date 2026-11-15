#![allow(dead_code)]
// A D-2(b) negative control (Clean docs/DECISIONS.md R215): the harness of `pm1_lower_role.rs`,
// its body the same verbatim aterm body (`f306a395db`), with its SPECS.md clause made FALSE
// for some input, so the harness panics there and no sound calculus certifies it: the
// row's harness form is not vacuous.

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
/// The table with Text->TextRun: false at Text.
pub fn lower_role_wrong(role: SemanticRole) -> u8 {
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
            SemanticRole::Text => Role::TextRun,
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
