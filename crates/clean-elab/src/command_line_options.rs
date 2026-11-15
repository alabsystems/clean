// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Command-line option overrides: Lean's `lean -D<name>=<value>`.
//!
//! Lake compiles every module of a package with the package's (and its
//! library's) `leanOptions`, which it hands to `lean` as `-D<name>=<value>`
//! arguments; `trust_ir-semantics` sets `autoImplicit := false` this way. A
//! frontend that ignores them elaborates a different language from the one the
//! package's real build checks: `theorem t (x : Foo) : x = x := rfl` with `Foo`
//! undefined auto-binds `Foo` and passes, where the package's build refuses it
//! with `unknown identifier 'Foo'` (gap G50).
//!
//! # What pinned Lean 4.8.0 does (measured on `bin/lean`, 2026-10-08)
//!
//! - `-Dname=value` and `-D name=value` are the same override; a later `-D`
//!   for a name wins.
//! - An argument with no `=` is refused: `invalid -D parameter, argument must
//!   contain '='`.
//! - A name no builtin option declares is refused before anything is
//!   elaborated: `invalid -D parameter, unknown configuration option 'bogus'`.
//! - A `Bool` option takes exactly `true` or `false`; anything else (`0`,
//!   `False`) is `invalid -D parameter, invalid configuration option
//!   'autoImplicit' value, it must be true/false`.
//! - A `Nat` option is read with C `atoi`: `-DmaxRecDepth=abc` is accepted as
//!   `0` (and then every declaration hits the recursion limit). Mirrored by
//!   [`lean_atoi`].
//! - A `String` option takes the text after `=` verbatim.
//! - Any other kind cannot be set from the command line (`invalid -D
//!   parameter, configuration option '…' cannot be set in the command line,
//!   use set_option command`); no option pinned Lean 4.8.0 declares has such
//!   a kind, so the table below holds none.
//!
//! An override is the INITIAL value of the option for every declaration of the
//! file — exactly a leading `set_option name value` — so an in-file
//! `set_option` still overrides it, and a `section` that sets it restores the
//! override at `end`. [`apply_command_line_options`] installs it through the
//! same two setters the file-scope `set_option` handler uses.
//!
//! # Which names are accepted
//!
//! The authority is pinned Lean, not Clean's registry: `lean_v4_8_0_options.tsv`
//! lists every option `bin/lean -D` accepts (342, measured), with its kind and
//! default. A name outside it is refused with Lean's unknown-option message —
//! including Clean's own registry extensions (`clean.inductive.*`,
//! `grind.warning`, `pp.parens`, …), which pinned Lean refuses, so a lakefile
//! that sets one fails under `lake build` and must fail here too. A pinned name
//! is then:
//!
//! - **applied** when Clean's registry
//!   ([`crate::options_registry::OptionsRegistry`]) declares it: installed as a
//!   leading `set_option`;
//! - **not applied, disclosed** when Clean does not implement it but it cannot
//!   change which declarations are accepted (`pp.*`, `trace.*`, `linter.*`,
//!   `format.*`, profiler and diagnostics output, see
//!   [`cannot_change_acceptance`]) or is set to Lean's own default (a no-op);
//!   [`CommandLineOption::is_applied`] is false and callers say so on stderr;
//! - **refused** otherwise ([`CommandLineOptionError::NotImplemented`]): an
//!   option such as `warningAsError=true` or `quotPrecheck=false` changes what
//!   Lean accepts, and elaborating without it could accept what the package's
//!   build refuses.

use crate::options_registry::standard_option_default;
use crate::FileContext;
use clean_kernel::Environment;
use std::collections::HashMap;
use std::sync::LazyLock;

/// The kind of a pinned-Lean option: exactly the kinds `-D` can set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PinnedKind {
    Bool,
    Nat,
    String,
}

/// One row of `lean_v4_8_0_options.tsv`.
#[derive(Debug, Clone, Copy)]
struct PinnedOption {
    kind: PinnedKind,
    default: &'static str,
}

/// Every option pinned Lean 4.8.0's `-D` accepts, by name. A malformed table
/// row is dropped, which makes its name unknown: a refusal, never an accept.
static PINNED_OPTIONS: LazyLock<HashMap<&'static str, PinnedOption>> = LazyLock::new(|| {
    include_str!("lean_v4_8_0_options.tsv")
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .filter_map(|line| {
            let mut cols = line.split('\t');
            let name = cols.next()?;
            let kind = match cols.next()? {
                "Bool" => PinnedKind::Bool,
                "Nat" => PinnedKind::Nat,
                "String" => PinnedKind::String,
                _ => return None,
            };
            let default = cols.next()?;
            Some((name, PinnedOption { kind, default }))
        })
        .collect()
});

/// The number of names in the pinned table (a test pins it at 342).
#[cfg(test)]
#[must_use]
pub(crate) fn pinned_lean_option_count() -> usize {
    PINNED_OPTIONS.len()
}

/// Whether an option Clean does not implement can change which declarations
/// Lean accepts. These only print, trace, lint (a warning, unless
/// `warningAsError`, which is not in this class), profile or format.
#[must_use]
pub(crate) fn cannot_change_acceptance(name: &str) -> bool {
    const PREFIXES: [&str; 8] = [
        "pp.",
        "trace.",
        "linter.",
        "format.",
        "profiler",
        "diagnostics",
        "server.",
        "infoview.",
    ];
    const NAMES: [&str; 7] = [
        "printMessageEndPos",
        "showPartialSyntaxErrors",
        "showTacticDiff",
        "showInferredTerminationBy",
        "guard_msgs.diff",
        "structureDiamondWarning",
        "tactic.simp.trace",
    ];
    PREFIXES.iter().any(|p| name.starts_with(p)) || NAMES.contains(&name)
}

/// One validated `-D` override: an option Clean's registry declares and a
/// value of that option's kind, rendered the way `set_option` stores it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommandLineOption {
    name: String,
    value: String,
    /// Whether Clean installs it; see the module docs.
    applied: bool,
}

/// Why a `-D` argument was refused. The messages are pinned Lean 4.8.0's.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CommandLineOptionError {
    /// The argument has no `=`.
    #[error("invalid -D parameter, argument must contain '='")]
    MissingEquals,
    /// No option of that name is declared.
    #[error("invalid -D parameter, unknown configuration option '{name}'")]
    UnknownOption {
        /// The option name as given.
        name: String,
    },
    /// A `Bool` option was given something other than `true` / `false`.
    #[error(
        "invalid -D parameter, invalid configuration option '{name}' value, it must be true/false"
    )]
    NotBool {
        /// The option name.
        name: String,
    },
    /// A pinned-Lean option Clean does not implement, set to a value other
    /// than Lean's default, that can change which declarations are accepted.
    /// Not a message pinned Lean prints: Lean would apply it.
    #[error(
        "-D {name}={value}: a Lean 4.8.0 option Clean does not implement, and this value can \
         change which declarations Lean accepts; refusing rather than elaborating under \
         different options"
    )]
    NotImplemented {
        /// The option name.
        name: String,
        /// The value as given.
        value: String,
    },
}

impl CommandLineOption {
    /// Parse and validate one `-D` argument, `name=value` (the text after
    /// `-D`).
    ///
    /// # Errors
    ///
    /// The [`CommandLineOptionError`] pinned Lean reports for the same
    /// argument.
    pub fn parse(arg: &str) -> Result<Self, CommandLineOptionError> {
        let (name, value) = arg
            .split_once('=')
            .ok_or(CommandLineOptionError::MissingEquals)?;
        Self::new(name.trim(), value)
    }

    /// Validate `name` / `value` as one override (the parts of `name=value`).
    ///
    /// # Errors
    ///
    /// As for [`Self::parse`], less the missing `=`.
    pub fn new(name: &str, value: &str) -> Result<Self, CommandLineOptionError> {
        let pinned =
            PINNED_OPTIONS
                .get(name)
                .ok_or_else(|| CommandLineOptionError::UnknownOption {
                    name: name.to_string(),
                })?;
        let value = match pinned.kind {
            PinnedKind::Bool => match value {
                "true" | "false" => value.to_string(),
                _ => {
                    return Err(CommandLineOptionError::NotBool {
                        name: name.to_string(),
                    })
                }
            },
            PinnedKind::Nat => lean_atoi(value).to_string(),
            PinnedKind::String => value.to_string(),
        };
        let applied = standard_option_default(name).is_some();
        if !applied && !cannot_change_acceptance(name) && value != pinned.default {
            return Err(CommandLineOptionError::NotImplemented {
                name: name.to_string(),
                value,
            });
        }
        Ok(Self {
            name: name.to_string(),
            value,
            applied,
        })
    }

    /// Whether Clean installs this override. `false` for a pinned-Lean option
    /// Clean does not implement that cannot change acceptance, or that is set
    /// to Lean's default; callers disclose it rather than drop it in silence.
    #[must_use]
    pub fn is_applied(&self) -> bool {
        self.applied
    }

    /// The option name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The value, as `set_option` stores it (`false`, `400000`, a string's text).
    #[must_use]
    pub fn value(&self) -> &str {
        &self.value
    }

    /// `name=value`, the argument of `-D` that reproduces this override.
    #[must_use]
    pub fn to_arg(&self) -> String {
        format!("{}={}", self.name, self.value)
    }
}

/// Whether pinned Lean 4.8.0's `-D` declares `name` as a `Nat` option (Lean
/// 4.30.0-rc2 refuses a non-numeral value for one, where 4.8.0 reads it with
/// `atoi`; `clean lean` reproduces either).
#[must_use]
pub fn is_pinned_nat_option(name: &str) -> bool {
    PINNED_OPTIONS
        .get(name)
        .is_some_and(|pinned| pinned.kind == PinnedKind::Nat)
}

/// Pinned Lean 4.8.0's default for `name`, spelled as `-D` takes it.
#[must_use]
pub fn pinned_option_default(name: &str) -> Option<&'static str> {
    PINNED_OPTIONS.get(name).map(|pinned| pinned.default)
}

/// Parse every `-D` argument, in order; the first refused one is the error.
///
/// # Errors
///
/// The first argument's [`CommandLineOptionError`].
pub fn parse_command_line_options<S: AsRef<str>>(
    args: &[S],
) -> Result<Vec<CommandLineOption>, CommandLineOptionError> {
    args.iter()
        .map(|arg| CommandLineOption::parse(arg.as_ref()))
        .collect()
}

/// What a `lean` argument list (Lake's `leanArgs` for a module) sets.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct LeanArgOptions {
    /// Every `-D` override, in order.
    pub options: Vec<CommandLineOption>,
    /// Every other argument, verbatim: flags of the `lean` process
    /// (`--tstack=…`, `-j`, `--load-dynlib=…`) that change no elaboration
    /// Clean performs. Returned so a caller can disclose them, never dropped
    /// in silence.
    pub not_applied: Vec<String>,
}

/// Read the `-D` overrides out of a `lean` argument list, as `lean` reads
/// them: `-Dname=value`, or `-D` followed by `name=value` as the next
/// argument.
///
/// # Errors
///
/// The first `-D` that pinned Lean refuses (a trailing `-D` with no argument
/// is [`CommandLineOptionError::MissingEquals`]).
pub fn options_from_lean_args<S: AsRef<str>>(
    args: &[S],
) -> Result<LeanArgOptions, CommandLineOptionError> {
    let mut out = LeanArgOptions::default();
    let mut iter = args.iter().map(<S as AsRef<str>>::as_ref);
    while let Some(arg) = iter.next() {
        if arg == "-D" {
            let value = iter.next().ok_or(CommandLineOptionError::MissingEquals)?;
            out.options.push(CommandLineOption::parse(value)?);
        } else if let Some(value) = arg.strip_prefix("-D") {
            out.options.push(CommandLineOption::parse(value)?);
        } else {
            out.not_applied.push(arg.to_string());
        }
    }
    Ok(out)
}

/// Install `options` as the initial option state of the file `file_ctx`
/// elaborates into `env`, in order (a later override of a name wins).
///
/// Exactly what a leading file-scope `set_option name value` does: the value
/// goes into the environment (read by every elaboration path through
/// `ElabCtx::get_option`) and into the file context (re-applied before every
/// ordinary declaration and rolled back to by a `section` that changes it).
/// Call it after the file context is created and before its first declaration.
pub fn apply_command_line_options(
    env: &mut Environment,
    file_ctx: &mut FileContext,
    options: &[CommandLineOption],
) {
    for option in options.iter().filter(|o| o.applied) {
        env.set_option(option.name.clone(), Some(option.value.clone()));
        file_ctx.set_option(option.name.clone(), Some(option.value.clone()));
    }
}

/// C `atoi` followed by the cast to `unsigned` that Lean's `-D` applies to a
/// `Nat` option: optional leading whitespace, an optional sign, then the
/// longest run of decimal digits; no digits reads as `0`, and a negative value
/// wraps (`-1` is `4294967295`). Out-of-range magnitudes saturate to the
/// `int` range first (C leaves that undefined; glibc and Darwin saturate).
#[must_use]
pub(crate) fn lean_atoi(text: &str) -> u32 {
    let trimmed = text.trim_start_matches([' ', '\t', '\n', '\r', '\x0b', '\x0c']);
    let (negative, digits) = match trimmed.as_bytes().first() {
        Some(b'-') => (true, &trimmed[1..]),
        Some(b'+') => (false, &trimmed[1..]),
        _ => (false, trimmed),
    };
    let magnitude = digits
        .bytes()
        .take_while(u8::is_ascii_digit)
        .fold(0_i64, |acc, d| {
            acc.saturating_mul(10).saturating_add(i64::from(d - b'0'))
        });
    let signed = if negative { -magnitude } else { magnitude };
    let clamped = signed.clamp(i64::from(i32::MIN), i64::from(i32::MAX));
    // The `(unsigned)` cast of an `int`: two's-complement reinterpretation.
    i32::try_from(clamped).map_or(0, |v| v as u32)
}

#[cfg(test)]
#[path = "command_line_options_tests.rs"]
mod tests;
