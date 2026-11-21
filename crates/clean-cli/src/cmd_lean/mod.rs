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
mod deps_json;
mod dialect;
mod elaborate;
mod features;
mod locate;
mod members;
mod message;
mod observer;
mod olean_output;
mod options;
mod run_main;

#[cfg(test)]
mod stable_input_tests;
#[cfg(test)]
mod stable_world_tests;

pub(crate) use features::FEATURES;

use argv::{CommandLine, Opt, Parsed, Refusal};
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
            if let Some(code) = act_on_immediate(dialect, &error.before, false) {
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
    let query = [Opt::PrintPrefix, Opt::PrintLibdir].into_iter().find(|query| {
        dialect == LeanDialect::V4_36_0 && line.options.iter().any(|parsed| parsed.opt == *query)
    });
    if let Some(code) = act_on_immediate(dialect, &line.options, query.is_some()) {
        return code;
    }
    if let Some(query) = query {
        return match stable_sdk_path(&cwd, query) {
            Ok(path) => {
                println!("{}", path.display());
                0
            }
            Err(error) => {
                eprintln!("clean: `lean`: {error}");
                1
            }
        };
    }
    run_file(dialect, line)
}

fn stable_sdk_path(cwd: &Path, query: Opt) -> anyhow::Result<PathBuf> {
    let selected = clean_olean::source_world_for_file(cwd, Some(clean_kernel::LeanWorld::Lean436))?;
    let clean_olean::ImportWorld::Explicit { lib, .. } =
        selected.imports().map_err(Clone::clone)?
    else {
        anyhow::bail!("the stable Lean SDK has no selected library");
    };
    let prefix = lib
        .parent()
        .and_then(Path::parent)
        .and_then(deps::sdk_prefix_from_executable)
        .ok_or_else(|| anyhow::anyhow!("could not resolve the selected stable Lean executable"))?;
    let library = prefix.join("lib/lean");
    if library.canonicalize()? != lib.canonicalize()? {
        anyhow::bail!("the stable Lean executable and selected library belong to different SDKs");
    }
    Ok(if query == Opt::PrintPrefix { prefix } else { library })
}

/// The text of `--help`: Clean's version line, Lean's option list, and what
/// Clean refuses.
fn help_text(dialect: LeanDialect) -> String {
    format!(
        "{}\n{}{}",
        dialect::version_line(dialect),
        dialect.help_body(),
        dialect::refusal_note(dialect)
    )
}

/// A command line `lean` rejects: its message, the version line and the help,
/// on the streams pinned Lean uses (4.8.0 prints the help body on stdout and
/// the rest on stderr; 4.30.0-rc2 prints all of it on stderr). Exit 1.
fn usage_error(dialect: LeanDialect, first: &str) -> i32 {
    let header = dialect::version_line(dialect);
    let body = format!("{}{}", dialect.help_body(), dialect::refusal_note(dialect));
    if dialect.is_modern() {
        eprint!("{first}{header}\n{body}");
    } else {
        eprintln!("{first}{header}");
        print!("{body}");
    }
    1
}

/// Options that end the run where they stand, in the order written.
fn act_on_immediate(dialect: LeanDialect, options: &[Parsed], sdk_query: bool) -> Option<i32> {
    for parsed in options {
        match parsed.opt {
            Opt::Help => {
                print!("{}", help_text(dialect));
                return Some(0);
            }
            Opt::Features => {
                // The stable command lists the optional LLVM backend when built with it.
                println!("[]");
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
            Opt::PrintPrefix if dialect != LeanDialect::V4_36_0 => {
                return Some(refuse_option(parsed, Refusal::PrintPrefix));
            }
            Opt::PrintLibdir if dialect != LeanDialect::V4_36_0 => {
                return Some(refuse_option(parsed, Refusal::PrintLibdir));
            }
            Opt::DepsJson if !dialect.is_modern() => {
                return Some(refuse_option(parsed, Refusal::DepsJson));
            }
            Opt::Refused(Refusal::Profile | Refusal::Stats) if sdk_query => {}
            Opt::Refused(refusal) => return Some(refuse_option(parsed, refusal)),
            Opt::OleanOutput if parsed.value.is_none() => {
                eprintln!("error: argument missing for option '-o'");
                return Some(1);
            }
            _ => {}
        }
    }
    None
}

fn refuse_option(parsed: &Parsed, refusal: Refusal) -> i32 {
    eprintln!(
        "clean: `lean {}` is not supported: {}",
        parsed.spelling,
        refusal.reason()
    );
    1
}

/// What the remaining options ask for.
#[derive(Default)]
struct Settings {
    run: bool,
    stdin: bool,
    root: Option<PathBuf>,
    json: bool,
    deps: bool,
    deps_json: bool,
    src_deps: bool,
    olean_output: Option<PathBuf>,
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
                Opt::DepsJson => settings.deps_json = true,
                Opt::SrcDeps => settings.src_deps = true,
                Opt::OleanOutput => settings.olean_output = Some(PathBuf::from(value)),
                Opt::Define => settings.defines.push(value),
                Opt::ErrorKind => settings.error_kinds.push(value),
                // `-q`: Clean prints no verbose messages to suppress.
                // The immediate options were acted on already.
                Opt::Quiet
                | Opt::Help
                | Opt::Features
                | Opt::Version
                | Opt::ShortVersion
                | Opt::Githash
                | Opt::PrintPrefix
                | Opt::PrintLibdir
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
fn missing_file(dialect: LeanDialect, file: &str, error: &std::io::Error) -> String {
    match dialect {
        LeanDialect::V4_8_0 => format!("file '{file}' not found"),
        LeanDialect::V4_30_0Rc2 => {
            format!("no such file or directory (error code: 4294967294)\n  file: {file}")
        }
        LeanDialect::V4_36_0 => {
            let code = error.raw_os_error().unwrap_or(2);
            format!("no such file or directory (error code: {code})\n  file: {file}")
        }
    }
}

/// Lean 4.36 replaces a failed byte and all immediately following UTF-8
/// continuation bytes with a single replacement character.
fn stable_source_text(bytes: Vec<u8>) -> String {
    let bytes = match String::from_utf8(bytes) {
        Ok(text) => return text,
        Err(error) => error.into_bytes(),
    };
    let mut text = String::with_capacity(bytes.len());
    let mut replacing = false;
    for chunk in bytes.utf8_chunks() {
        if !chunk.valid().is_empty() {
            text.push_str(chunk.valid());
            replacing = false;
        }
        if let Some(&first) = chunk.invalid().first() {
            if !replacing || first & 0xc0 != 0x80 {
                text.push('\u{fffd}');
            }
            replacing = true;
        }
    }
    text
}

/// Bytes to remove from the start of a stable source file. Leave its newline
/// in place so reported line numbers still include the directive line.
fn stable_language_prefix(source: &str) -> Result<usize, &str> {
    const PREFIX: &str = "#lang";
    let Some(rest) = source.strip_prefix(PREFIX) else {
        return Ok(0);
    };
    let line_end = rest.find('\n').unwrap_or(rest.len());
    let language = rest[..line_end].trim_matches([' ', '\t', '\r', '\n']);
    if language == "lean4" {
        Ok(PREFIX.len() + line_end)
    } else {
        Err(language)
    }
}

fn run_file(dialect: LeanDialect, line: CommandLine) -> i32 {
    let settings = Settings::read(&line.options);
    let stable = dialect == LeanDialect::V4_36_0;
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
    if settings.deps_json {
        let files = match line.run_file {
            Some((file, mut rest)) => {
                rest.insert(0, file);
                rest
            }
            None => line.operands,
        };
        return deps_json::print(dialect, settings.stdin, files);
    }
    let (file, program_args) = if let Some((file, args)) = line.run_file {
        (Some(file), args)
    } else if settings.run {
        match line.operands.split_first() {
            Some((file, rest)) => (Some(file.clone()), rest.to_vec()),
            None if stable && settings.stdin => (None, Vec::new()),
            None => return expected_one_file(dialect),
        }
    } else if stable && settings.stdin {
        let file = match line.operands.as_slice() {
            [] => None,
            [file] => Some(file.clone()),
            _ => return expected_one_file(dialect),
        };
        (file, Vec::new())
    } else if settings.stdin {
        (None, Vec::new())
    } else if line.operands.len() == 1 {
        (line.operands.first().cloned(), Vec::new())
    } else {
        return expected_one_file(dialect);
    };
    let mut text = match (file.as_deref(), stable && settings.stdin) {
        (None, _) | (_, true) => {
            let read = if stable {
                let mut bytes = Vec::new();
                std::io::stdin()
                    .read_to_end(&mut bytes)
                    .map(|_| stable_source_text(bytes))
            } else {
                std::io::read_to_string(std::io::stdin())
            };
            match read {
                Ok(text) => text,
                Err(error) => {
                    eprintln!("clean: `lean --stdin`: {error}");
                    return 1;
                }
            }
        }
        (Some(name), false) => {
            let read = if stable {
                std::fs::read(name).map(stable_source_text)
            } else {
                std::fs::read_to_string(name)
            };
            match read {
                Ok(text) => text,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    eprintln!("{}", missing_file(dialect, name, &error));
                    return 1;
                }
                Err(error) => {
                    eprintln!("clean: `lean {name}`: {error}");
                    return 1;
                }
            }
        }
    };
    let dependency_query = settings.deps || settings.src_deps;
    if stable && !dependency_query {
        let prefix = match stable_language_prefix(&text) {
            Ok(prefix) => prefix,
            Err(language) => {
                eprintln!("unknown language '{language}'\n");
                return 1;
            }
        };
        text.replace_range(..prefix, "");
    }
    let source_path = file.as_deref().map_or(Path::new("<stdin>"), Path::new);
    let source_world = match dialect
        .explicit_source_world()
        .map(|world| clean_olean::source_world_for_file(source_path, Some(world)))
        .transpose()
    {
        Ok(decision) => decision,
        Err(error) => {
            eprintln!("clean: `lean`: {error}");
            return 1;
        }
    };
    if dependency_query {
        // Stable Lean dispatches --deps before --src-deps regardless of argv order.
        let list_sources = settings.src_deps && !(stable && settings.deps);
        let (lines, error) =
            deps::dependency_lines(dialect, source_world.as_ref(), &text, list_sources);
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
    let main_module = match (&file, &settings.olean_output) {
        (None, _) => clean_kernel::Name::anon().str("_stdin"),
        (Some(name), None) => elaborate::main_module(Path::new(name), settings.root.as_deref()),
        (Some(name), Some(_)) => {
            match olean_output::module_name(Path::new(name), settings.root.as_deref()) {
                Ok(module) => module,
                Err(error) => {
                    eprintln!("{error:#}");
                    return 1;
                }
            }
        }
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
        source_world,
        native_main: stable && settings.run,
        olean_output: settings.olean_output,
    };
    let elaborated = match elaborate_on_large_stack(input, defines.options, render) {
        Ok(elaborated) => elaborated,
        Err(message) => {
            eprintln!("{message}");
            return 1;
        }
    };
    match elaborated {
        elaborate::Elaboration::Failed => 1,
        elaborate::Elaboration::Checked => match (&file, settings.run) {
            (Some(file), true) => run_main::run_main(Path::new(file), &program_args),
            _ => 0,
        },
        elaborate::Elaboration::Native(artifact) => {
            run_main::run_artifact(Ok(artifact), &program_args)
        }
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
) -> Result<elaborate::Elaboration, String> {
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
        Ok(Ok(elaborated)) => Ok(elaborated),
        Ok(Err(error)) => Err(format!("clean: {error:#}")),
        Err(_) => Err("clean: the elaboration thread panicked".to_owned()),
    }
}
