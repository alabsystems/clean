// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The server's trust boundary (plan item `devsurface-server-trust-boundary`).
//!
//! # Who can reach the server
//!
//! Anyone who can open a connection to its port: every process on the machine,
//! whichever user runs it, and, through a browser there, any web page. A page
//! can open a WebSocket to `127.0.0.1` (its handshake carries the page's
//! `Origin`), and it can POST to the TCP port, whose transport reads lines: an
//! HTTP request's body line was read as a JSON-RPC request. What a request can
//! do: `saveEnvironment` writes a file wherever the server's user may write,
//! `loadEnvironment` and `importModule` read files wherever it may read, and
//! `loadEnvironment` with `replace_unchecked` and `importModule` install
//! declarations no kernel checked, on which every later verdict the server
//! gives any client rests. A peer that holds a connection without sending
//! anything holds one of the server's connection slots.
//!
//! # What the boundary refuses
//!
//! - A connection, on either transport, whose first message is not the request
//!   `authenticate` with the server's launch token ([`admit`]). The token is 32
//!   bytes from the operating system's random source, new at every launch; the
//!   server writes it to a file only its user can read (mode 0600) and prints it
//!   on standard error ([`write_token_file`], [`launch_banner`]). A client of
//!   the same user reads the file (`client_launch_token`), and sends the default
//!   file's token only to `127.0.0.1`, the one address the server binds
//!   ([`client_token_from`]): any other address, `localhost`'s `::1` and the
//!   rest of 127/8 included, is one another user can listen on. A client asked
//!   for `localhost` connects to `127.0.0.1` ([`client_address`]). So only a
//!   server bound to `127.0.0.1` writes the default file: one bound elsewhere
//!   would hand its token to whoever listens on `127.0.0.1` at its port
//!   ([`default_token_file_address`]).
//! - A first message that does not arrive within the authenticate deadline of
//!   the connection's opening, a WebSocket handshake included
//!   ([`unauthorized_idle`]), and, on TCP, a first line longer than
//!   [`AUTHENTICATE_LINE_LIMIT`], refused before the rest of it is read: what
//!   a peer without the token can make the server hold is bounded in time and
//!   in bytes.
//! - A WebSocket handshake whose `Origin` is not on the server's allow-list,
//!   which is empty unless the operator names an origin ([`origin_refusal`]). A
//!   handshake without `Origin` (a client that is not a browser) is admitted to
//!   the token check.
//! - A path given to `saveEnvironment`, `loadEnvironment` or `importModule`
//!   that does not resolve under the workspace root, through every symbolic
//!   link it names, whether or not the file exists yet ([`confine`]). A
//!   relative path is relative to the root. Each module file `importModule`
//!   reads from one of the client's search paths, the requested module's and
//!   every one an `.olean` header in its import graph lists, must resolve under
//!   that search path too, with the parts beside it, and under the root's real
//!   path as the server fixed it at launch, since the search path was confined
//!   before the load waited for its turn and may have been swapped since; and
//!   no import may be named by a path that leaves the directory it is searched
//!   in ([`ModuleSearch::check`], asked by the load before it reads each file).
//! - `replace_unchecked` and `importModule` without the launch token in the
//!   request's own params ([`check_replace_token`], [`check_import_token`]):
//!   the token on the connection is not enough for the two requests that make
//!   later verdicts rest on declarations no kernel checked.
//!
//! What it does not cover: a process that can read the server's user's files
//! can read the token, and is that user as far as the server can tell. The
//! confinement is decided before the method runs, and the method then opens
//! its path again, so a process that can change links under the root between
//! the two (and holds the token) can still redirect a file method. For
//! `importModule`, a file found in a client's search path is judged against
//! the root as fixed at launch, so it is read from outside the root only
//! through a link changed between that file's check and its read; a search
//! path swapped after it was confined for a link to another directory under
//! the root still moves the walk there.
//! A module file found in the operator's search paths is not judged
//! beyond its name, so what those directories hold, links included, is read as
//! the operator laid it out. Peers that keep opening connections can still
//! keep the slots full, each one for at most the deadline. A WebSocket's first
//! message is bounded by the transport's message limit, not by the
//! authenticate line limit.

use std::borrow::Cow;
use std::ffi::OsString;
use std::fs::{self, OpenOptions};
use std::io::{self, Read, Write};
use std::net::SocketAddr;
use std::path::{Component, Path, PathBuf};
use std::time::Duration;

use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_olean::{ImportError, LoadSummary, ModuleCache};

use crate::rpc::{parse_message, ParsedMessage, RequestId, Response, RpcError};
use crate::{LaunchToken, ServerError, TokenFile};

/// The method a connection's first message must be.
pub(crate) const AUTHENTICATE: &str = "authenticate";

/// Random bytes in a launch token (written as twice as many hex digits).
pub(crate) const TOKEN_BYTES: usize = 32;

/// The most symbolic links [`confine`] follows from one path (macOS's limit).
const MAX_LINKS: usize = 32;

/// The one address `clean server` binds (`127.0.0.1:<port>`), and so the one
/// host a client sends the default token file's token to.
const SERVER_HOST: &str = "127.0.0.1";

/// The refusal of a connection that has not presented the token.
pub(crate) fn unauthorized_missing() -> RpcError {
    RpcError::unauthorized(
        "unauthorized: a connection's first message must be the request \
         {\"jsonrpc\":\"2.0\",\"method\":\"authenticate\",\"params\":{\"token\":\"<launch token>\"},\
         \"id\":0}; `clean server` prints its launch token on standard error and writes it to \
         its token file",
    )
}

/// The refusal of a token that is not this server's.
pub(crate) fn unauthorized_mismatch() -> RpcError {
    RpcError::unauthorized("unauthorized: the token presented is not this server's launch token")
}

/// The refusal of a connection that sent no `authenticate` request within
/// `deadline` of connecting.
pub(crate) fn unauthorized_idle(deadline: Duration) -> RpcError {
    RpcError::unauthorized(format!(
        "unauthorized: the connection sent no authenticate request within {} ms of connecting",
        deadline.as_millis()
    ))
}

/// How long a connection has, from its opening, to present the token: its
/// first message (on WebSocket, its handshake too) must arrive within it.
pub(crate) const DEFAULT_AUTHENTICATE_TIMEOUT_MS: u64 = 10_000;

/// The longest first line, newline included, the TCP transport reads before it
/// judges it. An `authenticate` request is about 130 bytes; a longer first line
/// is refused once this many bytes have arrived without a newline, so a peer
/// without the token cannot make the server hold more.
pub(crate) const AUTHENTICATE_LINE_LIMIT: usize = 4096;

/// `TOKEN_BYTES` bytes from the operating system's random source, as lowercase
/// hex. There is no fallback: a server that cannot make a token cannot start.
pub(crate) fn random_token() -> Result<String, ServerError> {
    let mut bytes = [0u8; TOKEN_BYTES];
    read_random(&mut bytes)
        .map_err(|e| ServerError::LaunchToken(format!("cannot read random bytes: {e}")))?;
    Ok(bytes.iter().map(|b| format!("{b:02x}")).collect())
}

#[cfg(unix)]
fn read_random(bytes: &mut [u8]) -> io::Result<()> {
    fs::File::open("/dev/urandom")?.read_exact(bytes)
}

#[cfg(not(unix))]
fn read_random(_bytes: &mut [u8]) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "this platform has no random source the server reads",
    ))
}

/// A token as a server printed or wrote it: `2 * TOKEN_BYTES` hex digits
/// (surrounding whitespace ignored), lowercased; otherwise why it is not one.
pub(crate) fn parse_token(text: &str) -> Result<String, String> {
    let text = text.trim();
    let digits = 2 * TOKEN_BYTES;
    if text.len() != digits || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!(
            "expected {digits} hex digits, found {} characters",
            text.chars().count()
        ));
    }
    Ok(text.to_ascii_lowercase())
}

/// Whether `presented` is `expected`, comparing every byte whatever the first
/// difference (both are of a fixed, public length).
pub(crate) fn same_secret(expected: &str, presented: &str) -> bool {
    let (a, b) = (expected.as_bytes(), presented.as_bytes());
    a.len() == b.len() && a.iter().zip(b).fold(0u8, |acc, (x, y)| acc | (x ^ y)) == 0
}

/// The token a request's params present: `params.token`, a string.
fn presented_token(params: Option<&serde_json::Value>) -> Option<&str> {
    params?.get("token")?.as_str()
}

/// The answer to `authenticate`: success when `params.token` is `token`.
pub(crate) fn answer_authenticate(
    token: Option<&LaunchToken>,
    id: RequestId,
    params: Option<&serde_json::Value>,
) -> Response {
    match (token, presented_token(params)) {
        (Some(token), Some(presented)) if token.matches(presented) => {
            Response::success(id, serde_json::json!({ "authenticated": true }))
        }
        (_, None) => Response::error(id, unauthorized_missing()),
        _ => Response::error(id, unauthorized_mismatch()),
    }
}

/// What a connection's first message decides.
#[derive(Debug)]
pub(crate) enum Admission {
    /// It presented the token: send the answer (none for a notification) and
    /// dispatch every later message.
    Admitted(Option<Response>),
    /// Send the refusal and close the connection.
    Refused(Response),
}

/// Judge a connection's first message: only `authenticate` with `token`
/// admits it. Nothing it asks for is dispatched.
pub(crate) fn admit(first: &str, token: Option<&LaunchToken>) -> Admission {
    let request = match parse_message(first) {
        Ok(ParsedMessage::Single(request)) => request,
        // A batch, a parse error, an HTTP request line: no token presented.
        _ => return Admission::Refused(Response::error(RequestId::Null, unauthorized_missing())),
    };
    let id = request.id.clone().unwrap_or(RequestId::Null);
    if request.method != AUTHENTICATE {
        return Admission::Refused(Response::error(id, unauthorized_missing()));
    }
    let answer = answer_authenticate(token, id, request.params.as_ref());
    if answer.error.is_some() {
        Admission::Refused(answer)
    } else if request.is_notification() {
        Admission::Admitted(None)
    } else {
        Admission::Admitted(Some(answer))
    }
}

/// The body of a refused WebSocket handshake, or `None` when `origin` may
/// connect: no `Origin` header (not a browser), or one on `allowed` (compared
/// without regard to ASCII case).
pub(crate) fn origin_refusal(origin: Option<&str>, allowed: &[String]) -> Option<String> {
    let origin = origin?.trim();
    if allowed
        .iter()
        .any(|a| a.trim().eq_ignore_ascii_case(origin))
    {
        return None;
    }
    Some(format!(
        "clean-server refuses a WebSocket connection from origin `{origin}`: the origin is not \
         on the server's allow-list, which is empty unless `clean server --allow-origin` names it"
    ))
}

/// `loadEnvironment`'s `replace_unchecked`: refused unless the request's own
/// `params.token` is the launch token.
pub(crate) fn check_replace_token(
    token: Option<&LaunchToken>,
    presented: Option<&str>,
) -> Result<(), RpcError> {
    check_params_token(
        token,
        presented,
        "loadEnvironment refuses replace_unchecked",
    )
}

/// `importModule`: refused unless the request's own `params.token` is the
/// launch token. What it imports is installed with structural checks only
/// (`clean_olean`'s `extend_constants_structural`), and nothing in the server
/// re-checks it before a verdict cites it, as with `replace_unchecked`.
pub(crate) fn check_import_token(
    token: Option<&LaunchToken>,
    presented: Option<&str>,
) -> Result<(), RpcError> {
    check_params_token(token, presented, "importModule refuses")
}

/// Refused (`refusing` opens the message) unless `presented` is `token`.
fn check_params_token(
    token: Option<&LaunchToken>,
    presented: Option<&str>,
    refusing: &str,
) -> Result<(), RpcError> {
    match (token, presented) {
        (Some(token), Some(presented)) if token.matches(presented) => Ok(()),
        (_, None) => Err(RpcError::unauthorized(format!(
            "{refusing} without the server's launch token: pass it as params.token"
        ))),
        _ => Err(RpcError::unauthorized(format!(
            "{refusing}: params.token is not this server's launch token"
        ))),
    }
}

/// The path a file method uses for `requested` (relative to `root` when it is
/// relative), refused with a named error unless it resolves under `root`.
/// `method` and `what` name the request and the operand in the refusal.
pub(crate) fn confine(
    method: &str,
    what: &str,
    requested: &str,
    root: Option<&Path>,
) -> Result<PathBuf, RpcError> {
    let Some(root) = root else {
        return Err(RpcError::outside_workspace(format!(
            "{method} refuses {what} `{requested}`: the server has no workspace root"
        )));
    };
    let joined = root.join(requested);
    match real_location(&joined) {
        Ok(real) if real.starts_with(root) => Ok(joined),
        Ok(real) => Err(RpcError::outside_workspace(format!(
            "{method} refuses {what} `{requested}`: it resolves to `{}`, which is not under the \
             workspace root `{}`",
            real.display(),
            root.display()
        ))),
        Err(error) => Err(RpcError::outside_workspace(format!(
            "{method} refuses {what} `{requested}`: it does not resolve to a location the \
             workspace root `{}` could contain: {error}",
            root.display()
        ))),
    }
}

/// Where `path` is, or would be once created: its real path when it exists;
/// otherwise the real path of the nearest existing ancestor (each symbolic
/// link on the way followed, a dangling one too) with the missing names
/// appended. A missing name cannot be a link, so the result is the location
/// the system would open.
fn real_location(path: &Path) -> io::Result<PathBuf> {
    let mut current = path.to_path_buf();
    // The names below `current` that do not exist, innermost first.
    let mut missing: Vec<OsString> = Vec::new();
    let mut links = 0;
    loop {
        if let Ok(real) = fs::canonicalize(&current) {
            return Ok(missing.iter().rev().fold(real, |at, name| at.join(name)));
        }
        let is_link = fs::symlink_metadata(&current).is_ok_and(|m| m.file_type().is_symlink());
        if is_link {
            if links == MAX_LINKS {
                return Err(io::Error::other(format!(
                    "more than {MAX_LINKS} symbolic links to follow"
                )));
            }
            links += 1;
            let target = fs::read_link(&current)?;
            current = if target.is_relative() {
                directory_of(&current).join(target)
            } else {
                target
            };
            continue;
        }
        let (Some(name), Some(parent)) = (current.file_name(), current.parent()) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "it names no file (it ends in `..`)",
            ));
        };
        missing.push(name.to_os_string());
        current = if parent.as_os_str().is_empty() {
            PathBuf::from(".")
        } else {
            parent.to_path_buf()
        };
    }
}

fn directory_of(path: &Path) -> &Path {
    match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    }
}

/// `importModule`'s module name: refused when a `.`-separated component holds
/// a path separator, which made the component a path (an absolute one replaced
/// the search path, so the name read the `.olean` it spelled, anywhere).
pub(crate) fn check_module_name(module: &str) -> Result<(), RpcError> {
    if module
        .split('.')
        .any(|c| c.contains('/') || c.contains('\\'))
    {
        return Err(RpcError::invalid_params(format!(
            "importModule refuses module `{module}`: a module name's components cannot contain a \
             path separator"
        )));
    }
    Ok(())
}

/// `importModule`'s search: the operator's search paths
/// (`clean_olean::default_search_paths()`), then the client's, each confined
/// under the workspace root by [`confine`], in the order `clean_olean`
/// searches them; and the check each module file the load resolves in it must
/// pass before the file is read ([`ModuleSearch::check`]).
#[derive(Debug, Clone)]
pub(crate) struct ModuleSearch {
    /// The module the client asked for, as it spelled it.
    requested: String,
    /// `requested` as `clean_olean` reads a dotted name.
    root: Name,
    /// The operator's search paths, then the client's.
    paths: Vec<PathBuf>,
    /// Where the client's search paths start in `paths`.
    client_from: usize,
    /// The workspace root the client's search paths were confined under, as
    /// the real path the server fixed when it started
    /// (`ServerState::workspace_root`). Each module file found in one of them
    /// must resolve under it when the load reaches the file, however the
    /// search path resolves by then. `None` when the server has none, and then
    /// every file found in a client's search path is refused.
    workspace: Option<PathBuf>,
}

impl ModuleSearch {
    /// The search for `requested` through the operator's `defaults`, then the
    /// client's `confined` search paths, which [`confine`] admitted under
    /// `workspace`, the workspace root's real path.
    pub(crate) fn new(
        requested: &str,
        defaults: Vec<PathBuf>,
        confined: Vec<PathBuf>,
        workspace: Option<&Path>,
    ) -> Self {
        let root = requested
            .trim_matches('.')
            .split('.')
            .fold(Name::anon(), |parent, part| parent.str(part));
        let client_from = defaults.len();
        let mut paths = defaults;
        paths.extend(confined);
        Self {
            requested: requested.to_string(),
            root,
            paths,
            client_from,
            workspace: workspace.map(Path::to_path_buf),
        }
    }

    /// Load the requested module and its import graph into `env` through
    /// `cache`, the load asking [`Self::check`] about each module file before
    /// it reads it. A refusal is the check's (`-32007`), and nothing is
    /// installed; any other failure of the load is `-32603`.
    pub(crate) fn load(
        &self,
        env: &mut Environment,
        cache: &ModuleCache,
    ) -> Result<Vec<LoadSummary>, RpcError> {
        let mut refusal: Option<RpcError> = None;
        let loaded = clean_olean::load_module_with_deps_cached_guarded(
            env,
            &self.requested,
            &self.paths,
            cache,
            &mut |module: &Name, file: &Path, found_in: usize| {
                self.check(module, file, found_in).map_err(|error| {
                    let reason = error.message.clone();
                    refusal = Some(error);
                    ImportError::UnsupportedModule {
                        module: module.to_string(),
                        reason,
                    }
                })
            },
        );
        loaded.map_err(|error| {
            refusal.take().unwrap_or_else(|| {
                RpcError::internal_error(format!("Failed to import module: {error}"))
            })
        })
    }

    /// Whether the load may read `file`, which holds `module` (the requested
    /// module, or one an `.olean` header in its import graph lists) and was
    /// found in the search path `found_in`. Refused wherever it was found: a
    /// module named by a path that leaves the directory it is searched in (a
    /// component that is absolute or `..`), which reads whatever file the name
    /// spells. Refused when it was found in one of the client's search paths:
    /// a file, or an `.olean.server` or `.olean.private` part beside it, that
    /// does not resolve, through every symbolic link (a dangling one too),
    /// under the real location of that search path, and under the workspace
    /// root. Confining the search path alone admitted a link below it: with
    /// `oleans/Ext -> /elsewhere`, module `Ext.X` in search path `oleans` read
    /// `/elsewhere/X.olean`, and so did a module there whose header imports
    /// `Ext.X`. Judging the file against its search path alone admitted the
    /// search path swapped for a link out of the root after [`confine`]
    /// admitted it: the walk runs later, after the writer's turn, a work slot
    /// and a copy of the environment. A file found in one of the operator's
    /// search paths is not judged further: they may lie anywhere.
    pub(crate) fn check(
        &self,
        module: &Name,
        file: &Path,
        found_in: usize,
    ) -> Result<(), RpcError> {
        let imported = (*module != self.root).then(|| module.to_string());
        let subject = match &imported {
            None => "it".to_string(),
            Some(import) => format!("`{import}`, in its import graph,"),
        };
        let relative = clean_olean::typed_module_rel_path(module)
            .map_err(|error| self.refused(&format!("{subject} names no module file: {error}")))?;
        if relative
            .components()
            .any(|part| !matches!(part, Component::Normal(_)))
        {
            return Err(self.refused(&format!(
                "{subject} is named by the path `{}`, which leaves the directory it is searched \
                 in: a module name's components cannot be absolute or `..`",
                relative.display()
            )));
        }
        if found_in < self.client_from {
            return Ok(());
        }
        let Some(dir) = self.paths.get(found_in) else {
            return Err(self.refused(&format!(
                "{subject} was found in search path {found_in}, which the request does not have"
            )));
        };
        let Some(workspace) = self.workspace.as_deref() else {
            return Err(self.refused(&format!(
                "{subject} was found in the search path `{}`, and the server has no workspace \
                 root to judge it under",
                dir.display()
            )));
        };
        confine_module_parts(dir, workspace, file, imported.as_deref())
            .map_err(|reason| self.refused(&reason))
    }

    /// The refusal of the request, for `reason`.
    fn refused(&self, reason: &str) -> RpcError {
        RpcError::outside_workspace(format!(
            "importModule refuses module `{}`: {reason}",
            self.requested
        ))
    }
}

/// [`ModuleSearch::check`] for `file`, found in the client's search path
/// `dir`: the file and the parts beside it that are there (a dangling link
/// counts) must resolve under `dir`'s real location, and under `workspace`,
/// the workspace root's real path; otherwise why not. The file is the
/// requested module's, or, with `import`, that import's. `dir` is resolved
/// here, at the check, and so follows whatever `dir` has become since
/// [`confine`] admitted it; `workspace` was fixed when the server started, so
/// a `dir` swapped for a link out of the root reads nothing outside it.
fn confine_module_parts(
    dir: &Path,
    workspace: &Path,
    file: &Path,
    import: Option<&str>,
) -> Result<(), String> {
    let within = fs::canonicalize(dir).map_err(|error| {
        format!(
            "its search path `{}` does not resolve: {error}",
            dir.display()
        )
    })?;
    let its_file = |part: &Path| match import {
        None => format!("its file `{}`", part.display()),
        Some(import) => format!(
            "the file `{}` of `{import}`, in its import graph,",
            part.display()
        ),
    };
    for part in [
        file.to_path_buf(),
        file.with_extension("olean.server"),
        file.with_extension("olean.private"),
    ] {
        // A part that is not there, not even as a link, is not read.
        if fs::symlink_metadata(&part).is_err() {
            continue;
        }
        match real_location(&part) {
            Ok(real) if !real.starts_with(&within) => {
                return Err(format!(
                    "{} resolves to `{}`, which is not under its search path `{}`",
                    its_file(&part),
                    real.display(),
                    within.display()
                ));
            }
            Ok(real) if !real.starts_with(workspace) => {
                return Err(format!(
                    "{} resolves to `{}`, which is not under the workspace root `{}`",
                    its_file(&part),
                    real.display(),
                    workspace.display()
                ));
            }
            Ok(_) => {}
            Err(error) => {
                return Err(format!(
                    "{} does not resolve to a location its search path `{}` could contain: \
                     {error}",
                    its_file(&part),
                    within.display()
                ));
            }
        }
    }
    Ok(())
}

/// The per-user directory the default token files live in:
/// `$XDG_RUNTIME_DIR/clean` when that names an absolute directory, else
/// `$HOME/.clean/run`.
pub(crate) fn runtime_dir() -> Result<PathBuf, ServerError> {
    let absolute = |name: &str| {
        std::env::var_os(name)
            .map(PathBuf::from)
            .filter(|p| p.is_absolute())
    };
    if let Some(dir) = absolute("XDG_RUNTIME_DIR") {
        return Ok(dir.join("clean"));
    }
    if let Some(home) = absolute("HOME") {
        return Ok(home.join(".clean").join("run"));
    }
    Err(ServerError::TokenFile {
        path: "(runtime directory)".to_string(),
        reason: "neither XDG_RUNTIME_DIR nor HOME names an absolute directory; name a token file \
                 (`clean server --token-file <path>`)"
            .to_string(),
    })
}

/// The default token file of a server on `port`.
pub(crate) fn runtime_token_path(port: u16) -> Result<PathBuf, ServerError> {
    Ok(runtime_dir()?.join(format!("server-{port}.token")))
}

/// Write `token` to the file `file` names for a server bound to `addr`,
/// readable and writable by the server's user only (0600), replacing what was
/// there in one step (a temporary file renamed over it, so a link planted at
/// the path is replaced, never followed). The runtime directory is created,
/// 0700, and its default file is written only for a server bound to
/// `127.0.0.1` ([`default_token_file_address`]).
pub(crate) fn write_token_file(
    file: &TokenFile,
    addr: SocketAddr,
    token: &LaunchToken,
) -> Result<PathBuf, ServerError> {
    let path = match file {
        TokenFile::At(path) => path.clone(),
        TokenFile::RuntimeDir => {
            default_token_file_address(addr)?;
            let path = runtime_token_path(addr.port())?;
            create_private_dir(directory_of(&path))?;
            path
        }
    };
    let failed = |reason: String| ServerError::TokenFile {
        path: path.display().to_string(),
        reason,
    };
    let name = path
        .file_name()
        .ok_or_else(|| failed("it names no file".to_string()))?
        .to_string_lossy()
        .into_owned();
    let temporary = directory_of(&path).join(format!(".{name}.{}.writing", std::process::id()));
    let _ = fs::remove_file(&temporary);
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let written = options.open(&temporary).and_then(|mut f| {
        f.write_all(token.as_str().as_bytes())?;
        f.write_all(b"\n")?;
        f.sync_all()
    });
    if let Err(e) = written.and_then(|()| fs::rename(&temporary, &path)) {
        let _ = fs::remove_file(&temporary);
        return Err(failed(e.to_string()));
    }
    Ok(path)
}

/// Refused unless a server bound to `addr` may write the default token file of
/// its port: unless `addr` is `127.0.0.1`. A client sends that file's token to
/// `127.0.0.1:<port>` alone ([`client_token_from`]), and while the server is
/// bound elsewhere any local user can listen there, so the file would hand the
/// server's token to that user. An explicitly named file is the operator's
/// choice: a client reads it only when `CLEAN_SERVER_TOKEN_FILE` names it.
pub(crate) fn default_token_file_address(addr: SocketAddr) -> Result<(), ServerError> {
    if addr.ip().to_string() == SERVER_HOST {
        return Ok(());
    }
    let port = addr.port();
    Err(ServerError::TokenFile {
        path: format!("server-{port}.token"),
        reason: format!(
            "the default token file is written only for a server bound to {SERVER_HOST}, and this \
             one is bound to {addr}: a client sends that file's token to {SERVER_HOST}:{port} \
             alone, where another local user can listen while this server is not there; bind \
             {SERVER_HOST}:{port}, or name the token file (`TokenFile::At`, `clean server \
             --token-file <path>`)"
        ),
    })
}

fn create_private_dir(dir: &Path) -> Result<(), ServerError> {
    let mut builder = fs::DirBuilder::new();
    builder.recursive(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(dir).map_err(|e| ServerError::TokenFile {
        path: dir.display().to_string(),
        reason: format!("cannot create the runtime directory: {e}"),
    })
}

/// The line a launch prints on standard error.
pub(crate) fn launch_banner(token: &LaunchToken, file: &Path, addr: SocketAddr) -> String {
    let token = token.as_str();
    format!(
        "clean-server: launch token {token} (also in {}, mode 0600); the first message on a \
         connection to {addr} must be \
         {{\"jsonrpc\":\"2.0\",\"method\":\"authenticate\",\"params\":{{\"token\":\"{token}\"}},\
         \"id\":0}}",
        file.display()
    )
}

/// The address a client of `server` (`host:port`) connects to: for
/// `localhost` (in any ASCII case) with a port, `127.0.0.1` with that port, the
/// one address `clean server` binds; any other spelling as it is. A resolver
/// asked for `localhost` may answer `::1` first (macOS's does), and any local
/// user can listen on `[::1]` at the server's port, so a client that let the
/// resolver choose could send its first message, the launch token, to another
/// user's process.
pub(crate) fn client_address(server: &str) -> Cow<'_, str> {
    match host_and_port(server) {
        Some((host, port)) if host.eq_ignore_ascii_case("localhost") => {
            Cow::Owned(format!("{SERVER_HOST}:{port}"))
        }
        _ => Cow::Borrowed(server),
    }
}

/// `server`'s host, as spelled, and port; `None` when it names no port.
fn host_and_port(server: &str) -> Option<(&str, u16)> {
    let (host, port) = server.rsplit_once(':')?;
    Some((host, port.parse().ok()?))
}

/// The token a client of `server` (`host:port`) presents: `CLEAN_SERVER_TOKEN`,
/// else the file `CLEAN_SERVER_TOKEN_FILE` names, else, when `server` is
/// `127.0.0.1`, the default token file of a server on that port.
pub(crate) fn client_token(server: &str) -> Result<LaunchToken, ServerError> {
    client_token_from(server, |name| std::env::var_os(name), runtime_token_path)
}

/// [`client_token`] over the environment `var` reads and the default token
/// file `default_file` names for a port.
pub(crate) fn client_token_from(
    server: &str,
    var: impl Fn(&str) -> Option<OsString>,
    default_file: impl Fn(u16) -> Result<PathBuf, ServerError>,
) -> Result<LaunchToken, ServerError> {
    if let Some(token) = var(CLIENT_TOKEN_ENV) {
        return parse_token(&token.to_string_lossy())
            .map(LaunchToken::from_parsed)
            .map_err(|reason| {
                ServerError::LaunchToken(format!(
                    "{CLIENT_TOKEN_ENV} is not a launch token: {reason}"
                ))
            });
    }
    let path = match var(CLIENT_TOKEN_FILE_ENV) {
        Some(path) => PathBuf::from(path),
        None => {
            let (host, port) = host_and_port(server).ok_or_else(|| {
                ServerError::LaunchToken(format!(
                    "`{server}` names no port, so the default token file is unknown; set \
                     {CLIENT_TOKEN_ENV} or {CLIENT_TOKEN_FILE_ENV}"
                ))
            })?;
            // The default file holds the token of the server on this port,
            // which binds 127.0.0.1 alone. Any other address may be another
            // user's listener: `::1` and the rest of 127/8 beside it, and a
            // name, which reaches whichever address answers first.
            if host != SERVER_HOST {
                return Err(ServerError::LaunchToken(format!(
                    "`{server}` is not {SERVER_HOST}, the one address `clean server` binds, so \
                     the default token file, which holds the token of the server there, is not \
                     sent to it; connect to {SERVER_HOST}:{port}, or set {CLIENT_TOKEN_ENV} or \
                     {CLIENT_TOKEN_FILE_ENV}"
                )));
            }
            default_file(port)?
        }
    };
    let text = fs::read_to_string(&path).map_err(|e| ServerError::TokenFile {
        path: path.display().to_string(),
        reason: format!(
            "cannot read the launch token ({e}); set {CLIENT_TOKEN_ENV} or \
             {CLIENT_TOKEN_FILE_ENV}, or start the server with its default token file"
        ),
    })?;
    parse_token(&text)
        .map(LaunchToken::from_parsed)
        .map_err(|reason| ServerError::TokenFile {
            path: path.display().to_string(),
            reason: format!("not a launch token: {reason}"),
        })
}

/// The environment variable a client reads the token from.
pub(crate) const CLIENT_TOKEN_ENV: &str = "CLEAN_SERVER_TOKEN";
/// The environment variable naming the file a client reads the token from.
pub(crate) const CLIENT_TOKEN_FILE_ENV: &str = "CLEAN_SERVER_TOKEN_FILE";

#[cfg(test)]
#[path = "trust_boundary_tests.rs"]
mod tests;
