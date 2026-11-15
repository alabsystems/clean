// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `lean -D name=value`, validated by G50's table
//! (`clean_elab::command_line_options`) and reported in the dialect's words.
//!
//! The table is pinned Lean 4.8.0's. Measured on `bin/lean` (2026-10-16), the
//! two releases word the same refusals differently:
//!
//! | case | 4.8.0 (stderr) | 4.30.0-rc2 |
//! |---|---|---|
//! | no `=` | `invalid -D parameter, argument must contain '='` | stderr, `error: ` prefixed |
//! | unknown name | `…unknown configuration option 'x'` | STDOUT, `<input>:1:0: error: …` plus a `-Dweak.x` hint (*) |
//! | bad `Bool` | `…invalid configuration option 'n' value, it must be true/false` | stderr, `error: `, quoting the VALUE |
//! | bad `Nat` | read with `atoi` (`abc` is 0) | stderr, `error: …it must be a natural number` |
//! | `-Dweak.x=v` | unknown option `weak.x` | set only when `x` exists, else nothing |
//!
//! (*) Not reproduced: the table is 4.8.0's, so a name it lacks may be a 4.30
//! option, and under the 4.30 dialect such a name is refused as Clean's
//! (`clean: … is not supported`) rather than with Lean's "unknown" text.
//!
//! `printMessageEndPos` is the front door's own: it changes how a message is
//! printed, which is this layer's job, so it is honoured here. A Lean option
//! Clean does not implement and that cannot change acceptance (`pp.*`,
//! `linter.*`, …) is accepted, and, unless it is set to Lean's own default (a
//! no-op), disclosed on stderr: Lean would print differently with it.

use super::dialect::LeanDialect;
use clean_elab::command_line_options::{
    is_pinned_nat_option, pinned_option_default, CommandLineOption, CommandLineOptionError,
};

/// A refused `-D`: what to print on stderr; the run exits 1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DefineRefusal {
    pub(crate) text: String,
}

/// The `-D` overrides of one run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Defines {
    /// What the elaborator gets (G50's overrides).
    pub(crate) options: Vec<CommandLineOption>,
    /// `printMessageEndPos`.
    pub(crate) print_end_pos: bool,
    /// Disclosures for stderr, one line each.
    pub(crate) notices: Vec<String>,
}

/// Validate every `-D` argument, in order; the first refusal ends the run.
pub(crate) fn read_defines(
    dialect: LeanDialect,
    args: &[String],
) -> Result<Defines, DefineRefusal> {
    let mut defines = Defines::default();
    for arg in args {
        let (raw_name, value) = match arg.split_once('=') {
            Some((name, value)) => (name.trim(), value),
            None => return Err(refusal(dialect, &CommandLineOptionError::MissingEquals, "")),
        };
        let (name, weak) = match raw_name.strip_prefix("weak.") {
            Some(name) if dialect.is_modern() => (name, true),
            _ => (raw_name, false),
        };
        if dialect.is_modern()
            && is_pinned_nat_option(name)
            && (value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()))
        {
            return Err(DefineRefusal {
                text: format!(
                    "error: invalid -D parameter, invalid configuration option '{value}' value, \
                     it must be a natural number\n"
                ),
            });
        }
        let option = match CommandLineOption::new(name, value) {
            Ok(option) => option,
            Err(CommandLineOptionError::UnknownOption { .. }) if weak => {
                defines.notices.push(format!(
                    "clean: -Dweak.{name}={value}: Clean declares no option `{name}`, so, as \
                     `weak.` asks, it was not set\n"
                ));
                continue;
            }
            Err(CommandLineOptionError::UnknownOption { .. }) if dialect.is_modern() => {
                // The table is 4.8.0's: a name it lacks may still be a 4.30
                // option, so Lean's "unknown option" text would be a guess.
                return Err(DefineRefusal {
                    text: format!(
                        "clean: `lean -D {name}={value}` is not supported: Clean's option table \
                         is pinned Lean 4.8.0's, which declares no option `{name}`\n"
                    ),
                });
            }
            Err(error) => return Err(refusal(dialect, &error, value)),
        };
        if option.name() == "printMessageEndPos" {
            defines.print_end_pos = option.value() == "true";
        } else if !option.is_applied()
            && pinned_option_default(option.name()) != Some(option.value())
        {
            defines.notices.push(format!(
                "clean: -D {}: a Lean option Clean does not implement; it cannot change which \
                 declarations are accepted, so it was not applied (messages may print \
                 differently from Lean's)\n",
                option.to_arg()
            ));
        }
        defines.options.push(option);
    }
    Ok(defines)
}

/// The dialect's words for a G50 refusal of `-D name=given`.
fn refusal(dialect: LeanDialect, error: &CommandLineOptionError, given: &str) -> DefineRefusal {
    let text = match error {
        CommandLineOptionError::NotImplemented { name, value } => {
            format!("clean: `lean -D {name}={value}` is not supported: {error}\n")
        }
        _ if !dialect.is_modern() => format!("{error}\n"),
        CommandLineOptionError::NotBool { .. } => format!(
            "error: invalid -D parameter, invalid configuration option '{given}' value, it must \
             be true/false\n"
        ),
        other => format!("error: {other}\n"),
    };
    DefineRefusal { text }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|arg| (*arg).to_owned()).collect()
    }

    #[test]
    fn test_define_refusals_use_each_dialects_words() {
        // Texts measured on pinned `lean -D…` of each release.
        let old = read_defines(LeanDialect::V4_8_0, &args(&["bogus=1"])).expect_err("unknown");
        assert_eq!(
            old,
            DefineRefusal {
                text: "invalid -D parameter, unknown configuration option 'bogus'\n".into()
            }
        );
        let old = read_defines(LeanDialect::V4_8_0, &args(&["pp.all"])).expect_err("no =");
        assert_eq!(
            old.text,
            "invalid -D parameter, argument must contain '='\n"
        );
        let new = read_defines(LeanDialect::V4_30_0Rc2, &args(&["pp.all"])).expect_err("no =");
        assert_eq!(
            new.text,
            "error: invalid -D parameter, argument must contain '='\n"
        );
        let new = read_defines(LeanDialect::V4_30_0Rc2, &args(&["autoImplicit=0"]))
            .expect_err("not a Bool");
        assert_eq!(
            new.text,
            "error: invalid -D parameter, invalid configuration option '0' value, it must be \
             true/false\n"
        );
        let new = read_defines(LeanDialect::V4_30_0Rc2, &args(&["maxRecDepth=abc"]))
            .expect_err("not a Nat");
        assert!(
            new.text.contains("must be a natural number"),
            "{}",
            new.text
        );
    }

    #[test]
    fn test_define_end_pos_and_defaults_are_silent() {
        let defines = read_defines(
            LeanDialect::V4_30_0Rc2,
            &args(&["printMessageEndPos=true", "linter.all=false"]),
        )
        .expect("accepted");
        assert!(defines.print_end_pos);
        assert!(defines.notices.is_empty(), "{:?}", defines.notices);
        // An option Clean declares (`pp.all`) is applied, so nothing to say.
        let defines = read_defines(LeanDialect::V4_8_0, &args(&["pp.all=true"])).expect("accepted");
        assert!(defines.notices.is_empty(), "{:?}", defines.notices);
        // A print-only Lean option Clean does not declare, set off its default,
        // is accepted and disclosed.
        let defines = read_defines(
            LeanDialect::V4_8_0,
            &args(&["trace.Meta.synthInstance.instances=true"]),
        )
        .expect("accepted");
        assert_eq!(defines.notices.len(), 1, "{:?}", defines.notices);
    }

    #[test]
    fn test_define_weak_unknown_is_disclosed_not_set() {
        let defines =
            read_defines(LeanDialect::V4_30_0Rc2, &args(&["weak.bogus=1"])).expect("weak");
        assert!(defines.options.is_empty());
        assert_eq!(defines.notices.len(), 1);
        assert!(read_defines(LeanDialect::V4_8_0, &args(&["weak.bogus=1"])).is_err());
    }

    #[test]
    fn test_define_acceptance_changing_unimplemented_option_is_refused() {
        let refused = read_defines(LeanDialect::V4_8_0, &args(&["warningAsError=true"]))
            .expect_err("changes acceptance");
        assert!(
            refused
                .text
                .starts_with("clean: `lean -D warningAsError=true` is not supported"),
            "{}",
            refused.text
        );
    }
}
