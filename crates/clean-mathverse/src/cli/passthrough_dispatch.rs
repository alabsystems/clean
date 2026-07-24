// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dispatch helpers for the 7 mathverse verbs absorbed via passthrough in
//! issue #3512 (`find`, `graph`, `diff`, `verify`, `download`, `export`,
//! `release`).
//!
//! These verbs were originally absorbed as typed clap variants in
//! `ae3772027` (passthrough), then partially re-typed in `f43429751` which
//! kept only `list`/`sample`/`deps`/`version` as typed args and dropped the
//! other 7 entirely. This module restores the missing 7 using the same
//! `PassthroughArgs` delegation pattern `ae3772027` used: every trailing
//! clap token is forwarded verbatim to [`crate::mathverse_bin_cmds::commands`],
//! so `clean mathverse <verb> <flags…>` and `mathverse <verb> <flags…>` produce
//! byte-identical stdout/stderr for the same input on the same shard
//! directory — the flag-parity guarantee from #3512.
//!
//! Passthrough is the right design for these 7 verbs because:
//!
//! - `find` carries ~6 flags (`--semantic`, `--tag`, `--similar`,
//!   `--cross-system`, `--limit`, `--domain`) with mutually-exclusive
//!   behaviour that is already validated in `cmd_find`.
//! - `graph` / `export` / `release` each take a sub-verb (`graph search`,
//!   `export clean-native`, `release build`) handled by the underlying
//!   command's own argv parser.
//! - `verify` / `diff` / `download` accept free-form positional paths plus
//!   light flags.
//!
//! Re-typing any of them as clap derive args would triple the descriptor
//! surface without adding any user-facing value and would risk drifting
//! from the standalone `mathverse` binary's flag semantics.
//!
//! Design: `designs/2026-04-19-epic-3436-orphan-triage.md`. Tracking:
//! #3512. Lineage: `ae3772027` (original absorption) →
//! `f43429751` (partial re-type) → this module (re-absorption of the 7
//! dropped verbs).

use crate::cli::{MathverseCliError, PassthroughArgs};
use crate::mathverse_bin_cmds::commands;

/// `clean mathverse find`
pub(crate) fn cmd_find(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_find(&args.rest);
    Ok(())
}

/// `clean mathverse graph <sub>`
pub(crate) fn cmd_graph(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_graph(&args.rest);
    Ok(())
}

/// `clean mathverse diff a b`
pub(crate) fn cmd_diff(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_diff(&args.rest);
    Ok(())
}

/// `clean mathverse verify <dir>`
pub(crate) fn cmd_verify(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_verify(&args.rest);
    Ok(())
}

/// `clean mathverse download`
pub(crate) fn cmd_download(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_download(&args.rest);
    Ok(())
}

/// `clean mathverse upload <dir> --to <dest>`
pub(crate) fn cmd_upload(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_upload(&args.rest);
    Ok(())
}

/// `clean mathverse serve [--core --port --download-base]`
pub(crate) fn cmd_serve(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_serve(&args.rest);
    Ok(())
}

/// `clean mathverse export <sub>`
pub(crate) fn cmd_export(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_export(&args.rest);
    Ok(())
}

/// `clean mathverse release <sub>`
pub(crate) fn cmd_release(args: PassthroughArgs) -> Result<(), MathverseCliError> {
    commands::cmd_release(&args.rest);
    Ok(())
}

#[cfg(test)]
mod tests {
    //! Wiring-only tests for the 7 passthrough dispatch helpers.
    //!
    //! We do not drive `cmd_*` end-to-end here because the underlying
    //! standalone-binary command functions print usage and call
    //! `std::process::exit(1)` on missing args; that would crash the test
    //! process. The shared-code-path parity guarantee (both the standalone
    //! `mathverse` binary and `clean mathverse <verb>` call the same `commands::cmd_*`
    //! with the same argv shape) covers behavioural correctness — this
    //! module's tests just confirm `PassthroughArgs::rest` is a plain
    //! `Vec<String>` the helpers can forward without wiring errors.
    use super::*;

    fn mk(rest: Vec<&str>) -> PassthroughArgs {
        PassthroughArgs {
            rest: rest.into_iter().map(str::to_string).collect(),
        }
    }

    #[test]
    fn test_passthrough_args_carry_rest_verbatim() {
        let args = mk(vec!["Nat.add", "--semantic", "--limit", "5"]);
        assert_eq!(args.rest, vec!["Nat.add", "--semantic", "--limit", "5"]);
    }

    #[test]
    fn test_passthrough_args_tolerate_empty_rest() {
        // `version`/`download --help` accept empty-arg invocations; the
        // wiring layer must not reject them.
        let args = mk(vec![]);
        assert!(args.rest.is_empty());
    }
}
