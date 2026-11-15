// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lean …` — and the `clean` binary invoked AS `lean` (a `lean`
//! symlink to it): a front door with `lean`'s command line and Lean's
//! semantics (decision R74).
//!
//! `clean check` is a verification verdict and fails closed on a file with no
//! declaration, on an explicit `sorry`, on an assumption it cannot credit.
//! `lean FILE` is not a verdict: it prints the messages the file logs and
//! exits 1 exactly when one of them is an error. A tool that runs `lean` (an
//! editor, a CI script, a test harness) needs THAT contract, so it gets its
//! own door instead of a weakened `clean check`. The door is one thin layer
//! over the module driver `clean check` runs (`elaborate.rs`): only the
//! observer that turns outcomes into messages (`observer.rs`) and the command
//! line (`argv.rs`) are its own.
//!
//! What it cannot honour it refuses by name (`clean: … is not supported:
//! <why>`, exit 1) and never ignores in silence.

mod argv;
mod deps;
mod dialect;
mod elaborate;
mod features;
mod locate;
mod members;
mod message;
mod observer;
mod options;
mod run_main;

pub(crate) use features::FEATURES;

use argv::{CommandLine, Opt, Parsed};
use dialect::LeanDialect;
use message::RenderOptions;
use std::ffi::OsString;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

/// `clean lean`'s clap surface, for the CLI registry and `clean help lean`.
/// The words are read raw from the process command line
/// ([`front_door_args`]), because clap's trailing-argument handling eats the
/// `--` that `lean` itself reads.
#[derive(clap::Args, Debug)]
#[command(disable_help_flag = true, disable_version_flag = true)]
pub(crate) struct LeanArgs {
    /// `lean`'s own command line: a file and `lean`'s flags
    /// (`clean lean --help` lists them).
    #[arg(trailing_var_arg = true, allow_hyphen_values = true, num_args = 0..)]
    pub(crate) args: Vec<String>,
}

/// The front door's words when this process is one: `clean lean <args>`, or
/// the binary invoked under the name `lean`.
pub(crate) fn front_door_args(argv: &[OsString]) -> Option<Vec<String>> {
    let invoked_as = argv
        .first()
        .map(Path::new)
        .and_then(Path::file_stem)
        .and_then(|stem| stem.to_str());
    let rest = if invoked_as == Some("lean") {
        &argv[1..]
    } else if argv.get(1).and_then(|arg| arg.to_str()) == Some("lean") {
        &argv[2..]
    } else {
        return None;
    };
    Some(
        rest.iter()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect(),
    )
}

/// Run the front door; the process's exit status.
pub(crate) fn run(args: &[String]) -> i32 {
    let code = run_inner(args);
    let _ = std::io::stdout().flush();
    code
}

fn run_inner(args: &[String]) -> i32 {
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let env_value = std::env::var(dialect::VERSION_ENV).ok();
    let dialect = match dialect::select(&cwd, env_value.as_deref()) {
        Ok(dialect) => dialect,
        Err(refusal) => {
            eprintln!("{}", refusal.0);
            return 1;
        }
    };
    let line = match argv::parse(dialect, args) {
        Ok(line) => line,
        Err(error) => {
            if let Some(code) = act_on_immediate(dialect, &error.before) {
                return code;
            }
            let mut first = String::new();
            if let Some(getopt) = error.getopt_line {
                first.push_str(&getopt);
                first.push('\n');
            }
            first.push_str("Unknown command line option\n");
            return usage_error(dialect, &first);
        }
    };
    if let Some(code) = act_on_immediate(dialect, &line.options) {
        return code;
    }
    run_file(dialect, line)
}

/// The text of `--help`: Clean's version line, Lean's option list, and what
/// Clean refuses.
fn help_text(dialect: LeanDialect) -> String {
    format!(
        "{}\n{}{}",
        dialect::version_line(dialect),
        dialect.help_body(),
        dialect::refusal_note()
    )
}

/// A command line `lean` rejects: its message, the version line and the help,
/// on the streams pinned Lean uses (4.8.0 prints the help body on stdout and
/// the rest on stderr; 4.30.0-rc2 prints all of it on stderr). Exit 1.
fn usage_error(dialect: LeanDialect, first: &str) -> i32 {
    let header = dialect::version_line(dialect);
    let body = format!("{}{}", dialect.help_body(), dialect::refusal_note());
    if dialect.is_modern() {
        eprint!("{first}{header}\n{body}");
    } else {
        eprintln!("{first}{header}");
        print!("{body}");
    }
    1
}

/// Options that end the run where they stand, in the order written.
fn act_on_immediate(dialect: LeanDialect, options: &[Parsed]) -> Option<i32> {
    for parsed in options {
        match parsed.opt {
            Opt::Help => {
                print!("{}", help_text(dialect));
                return Some(0);
            }
            Opt::Version => {
                println!("{}", dialect::version_line(dialect));
                return Some(0);
            }
            Opt::ShortVersion => {
                println!("{}", dialect::clean_version());
                return Some(0);
            }
            Opt::Githash => {
                return Some(match dialect::clean_git_sha() {
                    Some(sha) => {
                        println!("{sha}");
                        0
                    }
                    None => {
                        eprintln!(
                            "clean: `lean {}` is not supported: this Clean build has no git \
                             provenance, and Clean never prints a Lean commit",
                            parsed.spelling
                        );
                        1
                    }
                });
            }
            Opt::Refused(refusal) => {
                eprintln!(
                    "clean: `lean {}` is not supported: {}",
                    parsed.spelling,
                    refusal.reason()
                );
                return Some(1);
            }
            _ => {}
        }
    }
    None
}

/// What the remaining options ask for.
#[derive(Default)]
struct Settings {
    run: bool,
    stdin: bool,
    root: Option<PathBuf>,
    json: bool,
    deps: bool,
    src_deps: bool,
    defines: Vec<String>,
    error_kinds: Vec<String>,
}

impl Settings {
    fn read(options: &[Parsed]) -> Self {
        let mut settings = Self::default();
        for parsed in options {
            let value = parsed.value.clone().unwrap_or_default();
            match parsed.opt {
                Opt::RunFlag | Opt::RunFile => settings.run = true,
                Opt::Stdin => settings.stdin = true,
                Opt::Root => settings.root = Some(PathBuf::from(value)),
                Opt::Json => settings.json = true,
                Opt::Deps => settings.deps = true,
                Opt::SrcDeps => settings.src_deps = true,
                Opt::Define => settings.defines.push(value),
                Opt::ErrorKind => settings.error_kinds.push(value),
                // `-q`: Clean prints no verbose messages to suppress.
                // The immediate options were acted on already.
                Opt::Quiet
                | Opt::Help
                | Opt::Version
                | Opt::ShortVersion
                | Opt::Githash
                | Opt::Refused(_) => {}
            }
        }
        settings
    }
}

/// `Expected exactly one file name`.
fn expected_one_file(dialect: LeanDialect) -> i32 {
    usage_error(dialect, "Expected exactly one file name\n")
}

/// Pinned Lean's message for a missing input file (stderr).
fn missing_file(dialect: LeanDialect, file: &str) -> String {
    if dialect.is_modern() {
        format!("no such file or directory (error code: 4294967294)\n  file: {file}")
    } else {
        format!("file '{file}' not found")
    }
}

fn run_file(dialect: LeanDialect, line: CommandLine) -> i32 {
    let settings = Settings::read(&line.options);
    let defines = match options::read_defines(dialect, &settings.defines) {
        Ok(defines) => defines,
        Err(refusal) => {
            eprint!("{}", refusal.text);
            return 1;
        }
    };
    for notice in &defines.notices {
        eprint!("{notice}");
    }
    let (file, program_args) = if let Some((file, args)) = line.run_file {
        (Some(file), args)
    } else if settings.run {
        match line.operands.split_first() {
            Some((file, rest)) => (Some(file.clone()), rest.to_vec()),
            None => return expected_one_file(dialect),
        }
    } else if settings.stdin {
        (None, Vec::new())
    } else if line.operands.len() == 1 {
        (line.operands.first().cloned(), Vec::new())
    } else {
        return expected_one_file(dialect);
    };
    let text = match &file {
        None => {
            let mut text = String::new();
            if let Err(error) = std::io::stdin().read_to_string(&mut text) {
                eprintln!("clean: `lean --stdin`: {error}");
                return 1;
            }
            text
        }
        Some(name) => match std::fs::read_to_string(name) {
            Ok(text) => text,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                eprintln!("{}", missing_file(dialect, name));
                return 1;
            }
            Err(error) => {
                eprintln!("clean: `lean {name}`: {error}");
                return 1;
            }
        },
    };
    if settings.deps || settings.src_deps {
        let (lines, error) = deps::dependency_lines(dialect, &text, settings.src_deps);
        for path in lines {
            println!("{path}");
        }
        return match error {
            Some(message) => {
                eprintln!("{message}");
                1
            }
            None => 0,
        };
    }
    let main_module = match &file {
        None => clean_kernel::Name::anon().str("_stdin"),
        Some(name) => elaborate::main_module(Path::new(name), settings.root.as_deref()),
    };
    let render = RenderOptions {
        dialect,
        file_name: file.clone().unwrap_or_else(|| "<stdin>".to_owned()),
        json: settings.json,
        end_pos: defines.print_end_pos,
        error_kinds: settings.error_kinds,
    };
    let input = elaborate::Input {
        path: file.as_ref().map(PathBuf::from),
        text,
        main_module,
    };
    let error_logged = match elaborate_on_large_stack(input, defines.options, render) {
        Ok(error_logged) => error_logged,
        Err(message) => {
            eprintln!("{message}");
            return 1;
        }
    };
    match (&file, settings.run) {
        (Some(file), true) if !error_logged => run_main::run_main(Path::new(file), &program_args),
        _ => i32::from(error_logged),
    }
}

/// Stack for the elaboration thread: `clean check`'s
/// (`CHECK_THREAD_STACK_SIZE` in `lib.rs`), for the same reason — the parser,
/// elaborator and kernel recurse, and a deep term must not overflow a default
/// thread stack.
const STACK_SIZE: usize = 1024 * 1024 * 1024;

fn elaborate_on_large_stack(
    input: elaborate::Input,
    defines: Vec<clean_elab::command_line_options::CommandLineOption>,
    render: RenderOptions,
) -> Result<bool, String> {
    let handle = std::thread::Builder::new()
        .name("clean-lean".to_owned())
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let stdout = std::io::stdout();
            let mut out = stdout.lock();
            elaborate::elaborate(&input, &defines, &render, &mut out)
        })
        .map_err(|error| format!("clean: could not start the elaboration thread: {error}"))?;
    match handle.join() {
        Ok(Ok(error_logged)) => Ok(error_logged),
        Ok(Err(error)) => Err(format!("clean: {error:#}")),
        Err(_) => Err("clean: the elaboration thread panicked".to_owned()),
    }
}
