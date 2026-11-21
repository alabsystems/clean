// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `lean`'s command line, read the way pinned Lean's `getopt_long` reads it.
//!
//! Measured on `bin/lean` of both modelled releases (2026-10-16): options and
//! operands may be interleaved (`lean f.lean --json` works); `--` ends the
//! options; a long option may be abbreviated to any unique prefix (`--vers`)
//! and an ambiguous one is refused (`--s`); short options cluster (`-qv`) and
//! a short option's argument may be attached (`-Dname=v`) or the next word.
//! The option set is per release: Lean 4.8.0 rejects `-E`, `-V`,
//! `--src-deps` and `--setup` as unknown, and its `--run` is a flag (the file
//! is the first operand and the other operands are the program's arguments,
//! options still being read among them), while Lean 4.30.0-rc2's `--run`
//! takes the file and hands EVERYTHING after it to the program.
//!
//! Options are acted on in the order they are written, as Lean's `switch`
//! acts on each one as `getopt_long` returns it: `--version` exits before a
//! later bad option is read, and a refused option is refused where it stands.

use super::dialect::LeanDialect;

/// Whether an option takes an argument (`getopt_long`'s `has_arg`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HasArg {
    No,
    Required,
    /// Only as `--name=value`; a short spelling of the same option requires
    /// one.
    Optional,
}

/// Every option either release's `getopt_long` knows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Opt {
    Help,
    Features,
    Version,
    ShortVersion,
    Githash,
    /// Lean 4.8.0's `--run` / `-r` (both releases' `-r`): a flag.
    RunFlag,
    /// Lean 4.30.0-rc2's `--run <file>`.
    RunFile,
    Stdin,
    Root,
    Quiet,
    Json,
    Deps,
    DepsJson,
    SrcDeps,
    PrintPrefix,
    PrintLibdir,
    OleanOutput,
    Define,
    ErrorKind,
    /// Options Clean cannot honour; see [`Opt::refusal`].
    Refused(Refusal),
}

/// An option `clean lean` refuses, with the reason it gives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Refusal {
    Features,
    Olean,
    Ilean,
    COutput,
    Bitcode,
    Trust,
    Memory,
    Timeout,
    Threads,
    Tstack,
    Server,
    Worker,
    Plugin,
    LoadDynlib,
    Setup,
    DepsJson,
    PrintPrefix,
    PrintLibdir,
    Profile,
    Stats,
    ExitOnPanic,
    UndocumentedC,
    IncrementalSnapshot,
}

impl Refusal {
    /// Why Clean does not honour it.
    pub(crate) fn reason(self) -> &'static str {
        match self {
            Self::Features => "Clean does not report Lean compiler features",
            Self::Olean => "Clean does not write Lean-format `.olean` files for this dialect",
            Self::Ilean => "Clean does not write Lean `.ilean` files",
            Self::COutput => {
                "Clean does not emit Lean's C output (`clean compile --emit c` is Clean's own \
                 C emitter, not Lean's)"
            }
            Self::Bitcode => "Clean emits no LLVM bitcode",
            Self::Trust => {
                "Clean has no Lean trust levels; imported modules are loaded as Clean loads them"
            }
            Self::Memory => "Clean has no Lean memory limit",
            Self::Timeout => {
                "Clean has no Lean allocation-count timeout (its per-declaration budget is \
                 `clean check --decl-budget`)"
            }
            Self::Threads => "Clean elaborates a file on one thread and has no thread count",
            Self::Tstack => "Clean does not take a thread stack size",
            Self::Server | Self::Worker => {
                "Clean's language server is `clean lsp`, which does not speak Lean's \
                 server/worker protocol faithfully"
            }
            Self::Plugin => "Clean cannot load Lean shared-library plugins",
            Self::LoadDynlib => "Clean cannot load shared libraries into an interpreter",
            Self::Setup => "Clean does not read Lean's module-setup JSON",
            Self::DepsJson => "Clean does not print Lean's JSON dependency report",
            Self::PrintPrefix => "Clean has no Lean installation prefix",
            Self::PrintLibdir => "Clean has no Lean library directory",
            Self::Profile => "Clean prints no Lean profiler output",
            Self::Stats => "Clean prints no Lean environment statistics",
            Self::ExitOnPanic => "Clean has no Lean interpreter panic mode",
            Self::UndocumentedC => "it is an undocumented Lean option Clean does not model",
            Self::IncrementalSnapshot => "Clean does not read or write Lean incremental snapshots",
        }
    }
}

struct LongSpec {
    name: &'static str,
    has_arg: HasArg,
    opt: Opt,
    modern_only: bool,
}

const fn long(name: &'static str, has_arg: HasArg, opt: Opt, modern_only: bool) -> LongSpec {
    LongSpec {
        name,
        has_arg,
        opt,
        modern_only,
    }
}

/// The long options, as both releases' `g_long_options` declare them. `--run`
/// is listed twice, once per release.
const LONG: &[LongSpec] = &[
    long("help", HasArg::No, Opt::Help, false),
    long(
        "features",
        HasArg::Optional,
        Opt::Refused(Refusal::Features),
        false,
    ),
    long("version", HasArg::No, Opt::Version, false),
    long("short-version", HasArg::No, Opt::ShortVersion, true),
    long("githash", HasArg::No, Opt::Githash, false),
    long("run", HasArg::No, Opt::RunFlag, false),
    long("run", HasArg::Required, Opt::RunFile, true),
    long("o", HasArg::Optional, Opt::Refused(Refusal::Olean), false),
    long("i", HasArg::Optional, Opt::Refused(Refusal::Ilean), false),
    long("c", HasArg::Optional, Opt::Refused(Refusal::COutput), false),
    long(
        "bc",
        HasArg::Optional,
        Opt::Refused(Refusal::Bitcode),
        false,
    ),
    long("stdin", HasArg::No, Opt::Stdin, false),
    long("root", HasArg::Required, Opt::Root, false),
    long(
        "trust",
        HasArg::Required,
        Opt::Refused(Refusal::Trust),
        false,
    ),
    long("quiet", HasArg::No, Opt::Quiet, false),
    long(
        "memory",
        HasArg::Required,
        Opt::Refused(Refusal::Memory),
        false,
    ),
    long(
        "timeout",
        HasArg::Optional,
        Opt::Refused(Refusal::Timeout),
        false,
    ),
    long(
        "threads",
        HasArg::Required,
        Opt::Refused(Refusal::Threads),
        false,
    ),
    long(
        "tstack",
        HasArg::Required,
        Opt::Refused(Refusal::Tstack),
        false,
    ),
    long("server", HasArg::No, Opt::Refused(Refusal::Server), false),
    long("worker", HasArg::No, Opt::Refused(Refusal::Worker), false),
    long(
        "plugin",
        HasArg::Required,
        Opt::Refused(Refusal::Plugin),
        false,
    ),
    long(
        "load-dynlib",
        HasArg::Required,
        Opt::Refused(Refusal::LoadDynlib),
        false,
    ),
    long(
        "setup",
        HasArg::Required,
        Opt::Refused(Refusal::Setup),
        true,
    ),
    long("json", HasArg::No, Opt::Json, false),
    long("error", HasArg::Required, Opt::ErrorKind, true),
    long("deps", HasArg::No, Opt::Deps, false),
    long("deps-json", HasArg::No, Opt::DepsJson, false),
    long("src-deps", HasArg::No, Opt::SrcDeps, true),
    long("print-prefix", HasArg::No, Opt::PrintPrefix, false),
    long("print-libdir", HasArg::No, Opt::PrintLibdir, false),
    long("profile", HasArg::No, Opt::Refused(Refusal::Profile), false),
    long("stats", HasArg::No, Opt::Refused(Refusal::Stats), false),
    long(
        "exitOnPanic",
        HasArg::No,
        Opt::Refused(Refusal::ExitOnPanic),
        false,
    ),
];

const STABLE_LONG: &[LongSpec] = &[
    long("features", HasArg::No, Opt::Features, true),
    long(
        "incr-save",
        HasArg::Required,
        Opt::Refused(Refusal::IncrementalSnapshot),
        true,
    ),
    long(
        "incr-load",
        HasArg::Required,
        Opt::Refused(Refusal::IncrementalSnapshot),
        true,
    ),
    long(
        "incr-header-save",
        HasArg::Required,
        Opt::Refused(Refusal::IncrementalSnapshot),
        true,
    ),
];

/// The short options (`g_opt_str`), with whether each requires an argument.
fn short_spec(dialect: LeanDialect, ch: char) -> Option<(bool, Opt)> {
    let spec = match ch {
        'a' => (false, Opt::Refused(Refusal::Stats)),
        'b' => (true, Opt::Refused(Refusal::Bitcode)),
        'c' => (true, Opt::Refused(Refusal::COutput)),
        'd' => (false, Opt::Deps),
        'e' => (false, Opt::Refused(Refusal::ExitOnPanic)),
        'g' => (false, Opt::Githash),
        'h' => (false, Opt::Help),
        'i' => (true, Opt::Refused(Refusal::Ilean)),
        'j' => (true, Opt::Refused(Refusal::Threads)),
        'o' => (true, olean_option(dialect)),
        'p' => (true, Opt::Refused(Refusal::Plugin)),
        'q' => (false, Opt::Quiet),
        'r' if dialect == LeanDialect::V4_36_0 => (false, Opt::RunFile),
        'r' => (false, Opt::RunFlag),
        's' => (true, Opt::Refused(Refusal::Tstack)),
        't' => (true, Opt::Refused(Refusal::Trust)),
        'v' => (false, Opt::Version),
        'C' => (true, Opt::Refused(Refusal::UndocumentedC)),
        'D' => (true, Opt::Define),
        'M' => (true, Opt::Refused(Refusal::Memory)),
        'P' => (false, Opt::Refused(Refusal::Profile)),
        'R' => (true, Opt::Root),
        'T' => (true, Opt::Refused(Refusal::Timeout)),
        'E' if dialect.is_modern() => (true, Opt::ErrorKind),
        'V' if dialect.is_modern() => (false, Opt::ShortVersion),
        _ => return None,
    };
    Some(spec)
}

fn olean_option(dialect: LeanDialect) -> Opt {
    if dialect == LeanDialect::V4_36_0 {
        Opt::OleanOutput
    } else {
        Opt::Refused(Refusal::Olean)
    }
}

/// One option as `getopt_long` returned it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Parsed {
    pub(crate) opt: Opt,
    /// The spelling the user wrote (`-o`, `--o`, `--vers` …), for refusals.
    pub(crate) spelling: String,
    pub(crate) value: Option<String>,
}

/// What `getopt_long` makes of the whole command line.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct CommandLine {
    /// Options in the order written.
    pub(crate) options: Vec<Parsed>,
    /// Operands (permuted out of the options).
    pub(crate) operands: Vec<String>,
    /// A modern `--run <file> args…`: the file and the program's arguments.
    pub(crate) run_file: Option<(String, Vec<String>)>,
}

/// A command line `getopt_long` rejects, with its message (`lean: …`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UsageError {
    /// The `getopt` line, or `None` when Lean prints only its own
    /// `Unknown command line option`.
    pub(crate) getopt_line: Option<String>,
    /// Options read before the bad one (Lean acts on these first).
    pub(crate) before: Vec<Parsed>,
}

/// Read `args` (the words after `lean`).
pub(crate) fn parse(dialect: LeanDialect, args: &[String]) -> Result<CommandLine, UsageError> {
    let mut line = CommandLine::default();
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        index += 1;
        if arg == "--" {
            line.operands.extend(args[index..].iter().cloned());
            break;
        }
        if let Some(body) = arg.strip_prefix("--") {
            let (name, inline) = match body.split_once('=') {
                Some((name, value)) => (name, Some(value.to_owned())),
                None => (body, None),
            };
            let spec = find_long(dialect, name).map_err(|message| UsageError {
                getopt_line: Some(message),
                before: line.options.clone(),
            })?;
            // Stable Lean registers long --run as argument-free in getopt.
            // Its handler consumes the remaining argv starting at the file.
            let stable_run = dialect == LeanDialect::V4_36_0 && spec.opt == Opt::RunFile;
            let has_arg = if stable_run { HasArg::No } else { spec.has_arg };
            let value = match has_arg {
                HasArg::No => {
                    if inline.is_some() {
                        return Err(UsageError {
                            getopt_line: Some(format!(
                                "lean: option `--{}' doesn't allow an argument",
                                spec.name
                            )),
                            before: line.options,
                        });
                    }
                    None
                }
                HasArg::Optional => inline,
                HasArg::Required => match inline {
                    Some(value) => Some(value),
                    None if index < args.len() => {
                        index += 1;
                        Some(args[index - 1].clone())
                    }
                    None => {
                        return Err(UsageError {
                            getopt_line: Some(format!(
                                "lean: option `--{}' requires an argument",
                                spec.name
                            )),
                            before: line.options,
                        })
                    }
                },
            };
            if spec.opt == Opt::RunFile {
                line.run_file = if stable_run {
                    line.operands.clear();
                    args[index..]
                        .split_first()
                        .map(|(file, rest)| (file.clone(), rest.to_vec()))
                } else {
                    Some((value.unwrap_or_default(), args[index..].to_vec()))
                };
                line.options.push(Parsed {
                    opt: Opt::RunFile,
                    spelling: format!("--{name}"),
                    value: None,
                });
                break;
            }
            line.options.push(Parsed {
                opt: if spec.opt == Opt::Refused(Refusal::Olean) {
                    olean_option(dialect)
                } else {
                    spec.opt
                },
                spelling: format!("--{name}"),
                value,
            });
            continue;
        }
        if arg.len() > 1 && arg.starts_with('-') {
            let chars: Vec<char> = arg.chars().skip(1).collect();
            let mut at = 0;
            while at < chars.len() {
                let ch = chars[at];
                at += 1;
                let Some((needs_arg, opt)) = short_spec(dialect, ch) else {
                    let getopt_line =
                        (!matches!(ch, '0'..='2')).then(|| format!("lean: invalid option -- {ch}"));
                    return Err(UsageError {
                        getopt_line,
                        before: line.options,
                    });
                };
                let value = if needs_arg {
                    if at < chars.len() {
                        let rest: String = chars[at..].iter().collect();
                        at = chars.len();
                        Some(rest)
                    } else if index < args.len() {
                        index += 1;
                        Some(args[index - 1].clone())
                    } else {
                        return Err(UsageError {
                            getopt_line: Some(format!("lean: option requires an argument -- {ch}")),
                            before: line.options,
                        });
                    }
                } else {
                    None
                };
                if opt == Opt::RunFile {
                    line.operands.clear();
                    line.run_file = if at < chars.len() {
                        // In a short option cluster Lean keeps argv at the
                        // current word, so this entire word is its operand.
                        Some((arg.clone(), args[index..].to_vec()))
                    } else {
                        args[index..]
                            .split_first()
                            .map(|(file, rest)| (file.clone(), rest.to_vec()))
                    };
                    line.options.push(Parsed {
                        opt,
                        spelling: format!("-{ch}"),
                        value: None,
                    });
                    return Ok(line);
                }
                line.options.push(Parsed {
                    opt,
                    spelling: format!("-{ch}"),
                    value,
                });
            }
            continue;
        }
        line.operands.push(arg.clone());
    }
    Ok(line)
}

/// `getopt_long`'s lookup: an exact name, else a unique prefix.
fn find_long(dialect: LeanDialect, name: &str) -> Result<&'static LongSpec, String> {
    let visible = |spec: &&LongSpec| {
        if spec.opt == Opt::Refused(Refusal::Features) && dialect == LeanDialect::V4_36_0 {
            return false;
        }
        // Each release sees its own `--run`.
        let is_run = matches!(spec.opt, Opt::RunFlag | Opt::RunFile);
        if is_run {
            (spec.opt == Opt::RunFile) == dialect.is_modern()
        } else {
            !spec.modern_only || dialect.is_modern()
        }
    };
    let stable = if dialect == LeanDialect::V4_36_0 {
        STABLE_LONG
    } else {
        &[]
    };
    let options = LONG.iter().chain(stable).filter(visible);
    if let Some(spec) = options.clone().find(|spec| spec.name == name) {
        return Ok(spec);
    }
    let candidates: Vec<&LongSpec> = options
        .filter(|spec| !name.is_empty() && spec.name.starts_with(name))
        .collect();
    match candidates.as_slice() {
        [only] => Ok(*only),
        [] => Err(format!("lean: unrecognized option `--{name}'")),
        _ => Err(format!("lean: option `--{name}' is ambiguous")),
    }
}

#[cfg(test)]
#[path = "argv_tests.rs"]
mod tests;
