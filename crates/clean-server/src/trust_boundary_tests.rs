// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The pieces of the trust boundary one at a time (`trust_boundary.rs`); the
//! refusals as a client meets them are `tests/trust_boundary_tests.rs`.

use super::*;
use std::collections::HashMap;

/// A token no generator produces by chance, of the launch token's shape.
const TOKEN: &str = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";

fn token() -> LaunchToken {
    LaunchToken::parse(TOKEN).expect("a well-formed token")
}

fn real(path: &Path) -> PathBuf {
    fs::canonicalize(path).expect("canonicalize")
}

/// [`confine`]'s answer for a `path` operand, its refusal as the message.
fn confined(method: &str, requested: &str, root: &Path) -> Result<PathBuf, String> {
    confine(method, "path", requested, Some(root)).map_err(|e| e.message)
}

fn answer_json(response: &Response) -> String {
    serde_json::to_string(response).expect("a response serializes")
}

// ── the token ────────────────────────────────────────────────────────────────

#[test]
fn test_random_token_is_64_lowercase_hex_digits_and_new_each_time() {
    let first = random_token().expect("a random source");
    let second = random_token().expect("a random source");
    assert_eq!(first.len(), 2 * TOKEN_BYTES);
    assert!(
        first
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "{first}"
    );
    assert_ne!(first, second, "two launches share a token");
    assert_eq!(LaunchToken::parse(&first).expect("parses").as_str(), first);
}

#[test]
fn test_launch_token_parse_trims_and_folds_case_and_refuses_other_text() {
    let spelled = format!("  {}\n", TOKEN.to_ascii_uppercase());
    assert_eq!(
        LaunchToken::parse(&spelled).expect("parses").as_str(),
        TOKEN
    );

    let short = LaunchToken::parse("abc").expect_err("three digits are not a token");
    assert_eq!(
        short.to_string(),
        "launch token: expected 64 hex digits, found 3 characters"
    );
    let not_hex = format!("{}g", &TOKEN[..63]);
    let error = LaunchToken::parse(&not_hex).expect_err("`g` is not a hex digit");
    assert_eq!(
        error.to_string(),
        "launch token: expected 64 hex digits, found 64 characters"
    );
}

#[test]
fn test_launch_token_debug_never_shows_the_token() {
    let shown = format!("{:?}", token());
    assert_eq!(shown, "LaunchToken(<redacted>)");
    assert!(!shown.contains(TOKEN));
}

#[test]
fn test_same_secret_compares_every_byte_and_the_length() {
    assert!(same_secret(TOKEN, TOKEN));
    let last = format!("{}0", &TOKEN[..63]);
    assert!(!same_secret(TOKEN, &last), "a difference in the last byte");
    assert!(!same_secret(TOKEN, &TOKEN[..63]), "a prefix");
    assert!(!same_secret(TOKEN, ""), "nothing");
}

// ── a connection's first message ─────────────────────────────────────────────

#[test]
fn test_admit_authenticate_with_the_token_is_answered_and_admitted() {
    let first = format!(
        r#"{{"jsonrpc":"2.0","method":"authenticate","params":{{"token":"{TOKEN}"}},"id":0}}"#
    );
    match admit(&first, Some(&token())) {
        Admission::Admitted(Some(answer)) => assert_eq!(
            answer_json(&answer),
            r#"{"jsonrpc":"2.0","result":{"authenticated":true},"id":0}"#
        ),
        other => panic!("the token was not admitted: {other:?}"),
    }
    // As a notification it is admitted and answered with nothing.
    let notification =
        format!(r#"{{"jsonrpc":"2.0","method":"authenticate","params":{{"token":"{TOKEN}"}}}}"#);
    assert!(
        matches!(
            admit(&notification, Some(&token())),
            Admission::Admitted(None)
        ),
        "a notification presenting the token"
    );
}

#[test]
fn test_admit_refuses_anything_else_and_echoes_the_request_id() {
    let refused = |first: &str, token: Option<&LaunchToken>| match admit(first, token) {
        Admission::Refused(refusal) => refusal,
        Admission::Admitted(answer) => panic!("{first} was admitted: {answer:?}"),
    };
    let missing = unauthorized_missing().message;
    let mismatch = unauthorized_mismatch().message;

    let refusal = refused(
        r#"{"jsonrpc":"2.0","method":"serverInfo","id":7}"#,
        Some(&token()),
    );
    assert_eq!(refusal.id, RequestId::Number(7));
    let error = refusal.error.expect("an error");
    assert_eq!(
        (error.code, error.message.as_str()),
        (crate::rpc::error_codes::UNAUTHORIZED, missing.as_str())
    );

    let wrong = r#"{"jsonrpc":"2.0","method":"authenticate","params":{"token":"00"},"id":"a"}"#;
    let refusal = refused(wrong, Some(&token()));
    assert_eq!(refusal.id, RequestId::String("a".to_string()));
    assert_eq!(refusal.error.expect("an error").message, mismatch);

    let no_params = r#"{"jsonrpc":"2.0","method":"authenticate","id":1}"#;
    assert_eq!(
        refused(no_params, Some(&token()))
            .error
            .expect("an error")
            .message,
        missing
    );

    // A server with no token admits nobody, whatever is presented.
    let presented = format!(
        r#"{{"jsonrpc":"2.0","method":"authenticate","params":{{"token":"{TOKEN}"}},"id":0}}"#
    );
    assert_eq!(
        refused(&presented, None).error.expect("an error").message,
        mismatch
    );

    // A batch, a line that is not JSON and an HTTP request line present no
    // token, and their refusal has no id to echo.
    let batch = format!("[{presented}]");
    for first in [batch.as_str(), "{not json", "POST / HTTP/1.1"] {
        let refusal = refused(first, Some(&token()));
        assert_eq!(refusal.id, RequestId::Null, "{first}");
        assert_eq!(refusal.error.expect("an error").message, missing, "{first}");
    }
}

// ── the WebSocket Origin ─────────────────────────────────────────────────────

#[test]
fn test_origin_refusal_admits_no_origin_and_named_origins_only() {
    assert_eq!(
        origin_refusal(None, &[]),
        None,
        "a client that is not a browser"
    );
    let allowed = vec!["vscode-webview://abc".to_string()];
    assert_eq!(
        origin_refusal(Some("VSCODE-WEBVIEW://abc"), &allowed),
        None,
        "an allowed origin, compared without regard to case"
    );
    for origin in ["https://attacker.example", "null", "vscode-webview://abd"] {
        assert_eq!(
            origin_refusal(Some(origin), &allowed).as_deref(),
            Some(
                format!(
                    "clean-server refuses a WebSocket connection from origin `{origin}`: the \
                     origin is not on the server's allow-list, which is empty unless `clean \
                     server --allow-origin` names it"
                )
                .as_str()
            ),
            "{origin}"
        );
    }
    assert!(
        origin_refusal(Some("http://localhost"), &[]).is_some(),
        "the empty default list refuses every origin, the server's own host included"
    );
}

// ── replace_unchecked ────────────────────────────────────────────────────────

#[test]
fn test_check_replace_token_requires_this_servers_token() {
    assert!(check_replace_token(Some(&token()), Some(TOKEN)).is_ok());
    let messages = [
        (
            check_replace_token(Some(&token()), None),
            "loadEnvironment refuses replace_unchecked without the server's launch token: pass \
             it as params.token",
        ),
        (
            check_replace_token(Some(&token()), Some("00")),
            "loadEnvironment refuses replace_unchecked: params.token is not this server's \
             launch token",
        ),
        (
            check_replace_token(None, Some(TOKEN)),
            "loadEnvironment refuses replace_unchecked: params.token is not this server's \
             launch token",
        ),
    ];
    for (result, message) in messages {
        let error = result.expect_err("refused");
        assert_eq!(
            (error.code, error.message.as_str()),
            (crate::rpc::error_codes::UNAUTHORIZED, message)
        );
    }
}

// ── paths under the workspace root ───────────────────────────────────────────

#[test]
fn test_confine_admits_paths_under_the_root_existing_or_not() {
    let dir = tempfile::tempdir().expect("scratch");
    let root = real(dir.path());
    fs::create_dir(root.join("sub")).expect("sub");
    fs::write(root.join("sub/there.env"), b"x").expect("file");

    for (requested, expected) in [
        ("new.env", root.join("new.env")),
        ("sub/there.env", root.join("sub/there.env")),
        ("sub/../sub/new.env", root.join("sub/../sub/new.env")),
        ("missing/dir/new.env", root.join("missing/dir/new.env")),
    ] {
        assert_eq!(
            confined("saveEnvironment", requested, &root),
            Ok(expected),
            "{requested}"
        );
    }
    let absolute = root.join("sub/there.env");
    let absolute = absolute.to_string_lossy();
    assert_eq!(
        confined("loadEnvironment", &absolute, &root),
        Ok(root.join("sub/there.env"))
    );
}

#[test]
fn test_confine_refuses_what_resolves_outside_the_root() {
    let dir = tempfile::tempdir().expect("scratch");
    let base = real(dir.path());
    let root = base.join("root");
    let outside = base.join("outside");
    fs::create_dir(&root).expect("root");
    fs::create_dir(&outside).expect("outside");

    let refusal = |requested: &str| {
        confine("saveEnvironment", "path", requested, Some(&root))
            .expect_err("outside the root")
            .message
    };
    let outside_message = |requested: &str, resolved: &Path| {
        format!(
            "saveEnvironment refuses path `{requested}`: it resolves to `{}`, which is not under \
             the workspace root `{}`",
            resolved.display(),
            root.display()
        )
    };

    assert_eq!(
        refusal("../outside/x.env"),
        outside_message("../outside/x.env", &outside.join("x.env"))
    );
    let absolute = outside.join("x.env").to_string_lossy().into_owned();
    assert_eq!(
        refusal(&absolute),
        outside_message(&absolute, &outside.join("x.env"))
    );
    // A root that is a prefix of a sibling's name does not contain it.
    let sibling = base.join("rootless");
    fs::create_dir(&sibling).expect("sibling");
    let spelled = sibling.join("x.env").to_string_lossy().into_owned();
    assert_eq!(
        refusal(&spelled),
        outside_message(&spelled, &sibling.join("x.env"))
    );
    // `..` after a name that does not exist cannot be resolved, so it is refused.
    assert_eq!(
        refusal("missing/../../outside/x.env"),
        format!(
            "saveEnvironment refuses path `missing/../../outside/x.env`: it does not resolve to \
             a location the workspace root `{}` could contain: it names no file (it ends in \
             `..`)",
            root.display()
        )
    );

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        symlink(&outside, root.join("out")).expect("link to a directory outside");
        symlink(outside.join("later.env"), root.join("later.env")).expect("dangling link");
        symlink("../outside/rel.env", root.join("rel.env")).expect("relative dangling link");
        symlink(root.join("loop_b"), root.join("loop_a")).expect("loop a");
        symlink(root.join("loop_a"), root.join("loop_b")).expect("loop b");
        assert_eq!(
            refusal("out/x.env"),
            outside_message("out/x.env", &outside.join("x.env"))
        );
        assert_eq!(
            refusal("later.env"),
            outside_message("later.env", &outside.join("later.env"))
        );
        assert_eq!(
            refusal("rel.env"),
            outside_message("rel.env", &outside.join("rel.env"))
        );
        assert_eq!(
            refusal("loop_a"),
            format!(
                "saveEnvironment refuses path `loop_a`: it does not resolve to a location the \
                 workspace root `{}` could contain: more than 32 symbolic links to follow",
                root.display()
            )
        );
        // A link that stays inside the root is followed and admitted.
        symlink(root.join("inner.env"), root.join("inner_link.env")).expect("inner link");
        assert_eq!(
            confined("saveEnvironment", "inner_link.env", &root),
            Ok(root.join("inner_link.env"))
        );
    }
}

#[test]
fn test_confine_without_a_root_refuses_every_path() {
    let error = confine("importModule", "search path", "lib", None).expect_err("no root");
    assert_eq!(
        (error.code, error.message.as_str()),
        (
            crate::rpc::error_codes::OUTSIDE_WORKSPACE,
            "importModule refuses search path `lib`: the server has no workspace root"
        )
    );
}

#[test]
fn test_check_module_name_refuses_a_component_that_is_a_path() {
    assert!(check_module_name("Init.Data.Nat").is_ok());
    for module in ["Probe./etc/x", "A.b/c", "A.b\\c", "/abs"] {
        let error = check_module_name(module).expect_err("a path in the name");
        assert_eq!(
            (error.code, error.message.as_str()),
            (
                crate::rpc::error_codes::INVALID_PARAMS,
                format!(
                    "importModule refuses module `{module}`: a module name's components cannot \
                     contain a path separator"
                )
                .as_str()
            )
        );
    }
}

/// A module whose one declaration is the axiom `<stem>.a`, importing
/// `imports`, exported as `<stem>.olean` into `dir`.
#[cfg(unix)]
fn write_module(dir: &Path, stem: &str, imports: &[(&str, bool)]) {
    let mut env = Environment::default();
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: Name::from_string(&format!("{stem}.a")),
        level_params: vec![],
        type_: clean_kernel::Expr::prop(),
    })
    .expect("an axiom whose type is Prop is admitted");
    let bytes = clean_olean::OleanExporter::export_with_env(
        &env,
        imports,
        &[],
        "c0de000000000000000000000000000000000003",
    )
    .expect("export the fixture module");
    fs::write(dir.join(format!("{stem}.olean")), bytes).expect("write the fixture module");
}

/// Each module file the load reads from a client's search path, and each part
/// beside it, must resolve under that search path, the requested module's and
/// every one a header in its import graph lists: confining the search path
/// alone admitted a link below it (`Ext -> <outside>` read `<outside>/X.olean`
/// for `Ext.X`, and for `W`, whose header imports `Ext.X`). A link that stays
/// inside is followed, and a file found in one of the operator's search paths,
/// searched first, is not judged.
#[cfg(unix)]
#[test]
fn test_module_search_load_refuses_a_module_file_linked_out_of_its_search_path() {
    use std::os::unix::fs::symlink;
    let dir = tempfile::tempdir().expect("scratch");
    let base = real(dir.path());
    let defaults = base.join("defaults");
    let search = base.join("search");
    let outside = base.join("outside");
    for made in [
        &defaults,
        &outside,
        &search.join("Real"),
        &search.join("Sib"),
    ] {
        fs::create_dir_all(made).expect("directory");
    }
    write_module(&outside, "X", &[]);
    write_module(&search.join("Real"), "X", &[]);
    write_module(&search.join("Sib"), "X", &[]);
    write_module(&search, "W", &[("Ext.X", false)]);
    write_module(&search, "V", &[("Alias.X", false)]);
    symlink(&outside, search.join("Ext")).expect("a directory link out");
    symlink(search.join("Real"), search.join("Alias")).expect("a directory link inside");
    symlink(outside.join("X.olean"), search.join("Sib/X.olean.server")).expect("a part linked out");

    let cache = ModuleCache::new();
    // The modules a fresh environment loaded, or the refusal.
    let judged = |module: &str| {
        let mut env = Environment::new();
        ModuleSearch::new(
            module,
            vec![defaults.clone()],
            vec![search.clone()],
            Some(&base),
        )
        .load(&mut env, &cache)
        .map(|loaded| loaded.len())
        .map_err(|e| (e.code, e.message))
    };
    let outside_message = |module: &str, its_file: String| {
        format!(
            "importModule refuses module `{module}`: {its_file} resolves to `{}`, which is not \
             under its search path `{}`",
            outside.join("X.olean").display(),
            search.display()
        )
    };
    let outside_workspace = crate::rpc::error_codes::OUTSIDE_WORKSPACE;
    assert_eq!(
        judged("Ext.X"),
        Err((
            outside_workspace,
            outside_message(
                "Ext.X",
                format!("its file `{}`", search.join("Ext/X.olean").display())
            )
        ))
    );
    assert_eq!(
        judged("Sib.X"),
        Err((
            outside_workspace,
            outside_message(
                "Sib.X",
                format!("its file `{}`", search.join("Sib/X.olean.server").display())
            )
        ))
    );
    assert_eq!(
        judged("W"),
        Err((
            outside_workspace,
            outside_message(
                "W",
                format!(
                    "the file `{}` of `Ext.X`, in its import graph,",
                    search.join("Ext/X.olean").display()
                )
            )
        ))
    );
    for (admitted, modules) in [("Real.X", 1), ("Alias.X", 1), ("V", 2)] {
        assert_eq!(judged(admitted), Ok(modules), "{admitted}");
    }
    // A module found nowhere, and a name `clean_olean` refuses, read nothing:
    // the load's own error, not the confinement's.
    for unread in ["Missing.X", "", "Ext..X"] {
        let code = judged(unread).map_err(|(code, _)| code);
        assert_eq!(
            code,
            Err(crate::rpc::error_codes::INTERNAL_ERROR),
            "{unread:?}"
        );
    }
    // The operator's search paths come first and may lie anywhere.
    symlink(&outside, defaults.join("Ext")).expect("a default's link out");
    assert_eq!(judged("Ext.X"), Ok(1), "a file the defaults hold");
    assert_eq!(judged("W"), Ok(2), "an import the defaults hold");
}

/// An import named by a path that leaves the directory it is searched in reads
/// the file the name spells: the check refuses it wherever it was found, the
/// operator's search paths included, whose files are otherwise not judged.
#[test]
fn test_module_search_check_refuses_an_import_named_by_a_path_wherever_it_is_found() {
    let defaults = PathBuf::from("/defaults");
    let search = ModuleSearch::new(
        "W",
        vec![defaults.clone()],
        vec![PathBuf::from("/root/oleans")],
        Some(Path::new("/root")),
    );
    for (name, path) in [
        (
            Name::anon().str("/elsewhere").str("X"),
            "/elsewhere/X.olean",
        ),
        (Name::anon().str("..").str("..").str("X"), "../../X.olean"),
    ] {
        let judged = search
            .check(&name, &defaults.join(path), 0)
            .map_err(|e| (e.code, e.message));
        assert_eq!(
            judged,
            Err((
                crate::rpc::error_codes::OUTSIDE_WORKSPACE,
                format!(
                    "importModule refuses module `W`: `{name}`, in its import graph, is named by \
                     the path `{path}`, which leaves the directory it is searched in: a module \
                     name's components cannot be absolute or `..`"
                )
            )),
            "{name}"
        );
    }
    // A name of module components found in the operator's search paths is not
    // judged further, and neither touches the filesystem.
    let core = Name::anon().str("Init").str("Core");
    assert_eq!(
        search
            .check(&core, &defaults.join("Init/Core.olean"), 0)
            .map_err(|e| e.message),
        Ok(())
    );
}

/// A client's search path is confined when the request arrives, and the walk
/// that reads from it runs later, after the writer's turn, a work slot and a
/// copy of the environment. A search path swapped in that time for a link out
/// of the root, whether it was a directory (`s`), not there yet (`t`) or a
/// link inside the root (`u`), reads nothing outside the root: each file is
/// judged against the root's real path, which the server fixed when it
/// started. Judged against its search path alone, as it resolved at the check,
/// the file `<outside>/X.olean` lay under the swapped `s` and was read.
#[cfg(unix)]
#[test]
fn test_module_search_load_refuses_a_search_path_swapped_for_a_link_out_after_it_was_confined() {
    use std::os::unix::fs::symlink;
    let dir = tempfile::tempdir().expect("scratch");
    let base = real(dir.path());
    let root = base.join("root");
    let outside = base.join("outside");
    for made in [&root.join("s"), &root.join("real"), &outside] {
        fs::create_dir_all(made).expect("directory");
    }
    for holder in [&outside, &root.join("s"), &root.join("real")] {
        write_module(holder, "X", &[]);
    }
    symlink(root.join("real"), root.join("u")).expect("a link inside the root");

    // Each search, built as the request's first pool job builds it: confined
    // under the root while each search path lies under it.
    let searches: Vec<(&str, ModuleSearch)> = ["s", "t", "u"]
        .into_iter()
        .map(|requested| {
            let confined = confine("importModule", "search path", requested, Some(&root))
                .expect("the search path lies under the root when the request arrives");
            (
                requested,
                ModuleSearch::new("X", Vec::new(), vec![confined], Some(&root)),
            )
        })
        .collect();
    let cache = ModuleCache::new();
    let judged = |search: &ModuleSearch| {
        let mut env = Environment::new();
        search
            .load(&mut env, &cache)
            .map(|loaded| loaded.len())
            .map_err(|e| (e.code, e.message))
    };
    for (requested, search) in &searches {
        let before = judged(search).map_err(|(code, _)| code);
        let expected = if *requested == "t" {
            Err(crate::rpc::error_codes::INTERNAL_ERROR)
        } else {
            Ok(1)
        };
        assert_eq!(before, expected, "{requested} before the swap");
    }

    // Each search path becomes a link out of the root before the walk runs.
    fs::rename(root.join("s"), root.join("s-was")).expect("move s aside");
    fs::remove_file(root.join("u")).expect("remove the link u");
    for swapped in ["s", "t", "u"] {
        symlink(&outside, root.join(swapped)).expect("a search path linked out of the root");
    }

    for (requested, search) in &searches {
        assert_eq!(
            judged(search),
            Err((
                crate::rpc::error_codes::OUTSIDE_WORKSPACE,
                format!(
                    "importModule refuses module `X`: its file `{}` resolves to `{}`, which is \
                     not under the workspace root `{}`",
                    root.join(requested).join("X.olean").display(),
                    outside.join("X.olean").display(),
                    root.display()
                )
            )),
            "{requested} after the swap"
        );
        // Confined now, it would be refused before the load.
        assert_eq!(
            confine("importModule", "search path", requested, Some(&root)).map_err(|e| e.code),
            Err(crate::rpc::error_codes::OUTSIDE_WORKSPACE),
            "{requested} confined after the swap"
        );
    }
}

/// A file found in a client's search path is judged under the workspace root,
/// so a search built without one refuses it, before anything is resolved.
#[test]
fn test_module_search_check_without_a_workspace_root_refuses_a_client_search_path() {
    let search = ModuleSearch::new("X", Vec::new(), vec![PathBuf::from("/root/oleans")], None);
    let name = Name::anon().str("X");
    assert_eq!(
        search
            .check(&name, Path::new("/root/oleans/X.olean"), 0)
            .map_err(|e| (e.code, e.message)),
        Err((
            crate::rpc::error_codes::OUTSIDE_WORKSPACE,
            "importModule refuses module `X`: it was found in the search path `/root/oleans`, \
             and the server has no workspace root to judge it under"
                .to_string()
        ))
    );
}

// ── the token file ───────────────────────────────────────────────────────────

/// An address `clean server` binds.
fn server_addr() -> SocketAddr {
    "127.0.0.1:1".parse().expect("an address")
}

#[test]
fn test_write_token_file_writes_the_token_alone_readable_by_its_owner_only() {
    let dir = tempfile::tempdir().expect("scratch");
    let path = dir.path().join("server.token");
    let written =
        write_token_file(&TokenFile::At(path.clone()), server_addr(), &token()).expect("written");
    assert_eq!(written, path);
    assert_eq!(
        fs::read_to_string(&path).expect("read"),
        format!("{TOKEN}\n")
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = fs::metadata(&path).expect("metadata").permissions().mode();
        assert_eq!(mode & 0o777, 0o600, "mode {mode:o}");
    }
    let names: Vec<_> = fs::read_dir(dir.path())
        .expect("list")
        .map(|e| e.expect("entry").file_name())
        .collect();
    assert_eq!(
        names,
        vec![OsString::from("server.token")],
        "no temporary left"
    );
}

#[cfg(unix)]
#[test]
fn test_write_token_file_replaces_a_planted_link_and_never_writes_through_it() {
    let dir = tempfile::tempdir().expect("scratch");
    let victim = dir.path().join("victim");
    fs::write(&victim, b"keep").expect("victim");
    let path = dir.path().join("server.token");
    std::os::unix::fs::symlink(&victim, &path).expect("planted link");

    write_token_file(&TokenFile::At(path.clone()), server_addr(), &token()).expect("written");
    assert_eq!(fs::read(&victim).expect("victim"), b"keep");
    assert!(
        !fs::symlink_metadata(&path)
            .expect("metadata")
            .file_type()
            .is_symlink(),
        "the link was replaced by a file"
    );
    assert_eq!(
        fs::read_to_string(&path).expect("read"),
        format!("{TOKEN}\n")
    );
}

/// The default token file holds the token of the server at `127.0.0.1:<port>`,
/// and a client sends it there alone, so a server bound to any other address
/// that wrote it would hand its token to whoever listens on `127.0.0.1` at its
/// port. Such a launch is refused before anything is written; a named file is
/// written for it, since a client reads that file only when told to.
#[test]
fn test_announce_token_runtime_dir_for_a_server_off_127_0_0_1_is_refused() {
    for bound in [
        "[::1]:47613",
        "0.0.0.0:47613",
        "[::]:47613",
        "127.0.0.2:47613",
        "[::ffff:127.0.0.1]:47613",
        "192.0.2.1:47613",
    ] {
        let addr: SocketAddr = bound.parse().expect("an address");
        match crate::announce_token(Some(&TokenFile::RuntimeDir), addr, &token()) {
            Err(ServerError::TokenFile { path, reason }) => {
                assert_eq!(path, "server-47613.token", "{bound}");
                assert_eq!(
                    reason,
                    format!(
                        "the default token file is written only for a server bound to \
                         127.0.0.1, and this one is bound to {addr}: a client sends that file's \
                         token to 127.0.0.1:47613 alone, where another local user can listen \
                         while this server is not there; bind 127.0.0.1:47613, or name the token \
                         file (`TokenFile::At`, `clean server --token-file <path>`)"
                    ),
                    "{bound}"
                );
            }
            other => panic!("{bound}: the default token file was not refused: {other:?}"),
        }
    }
    default_token_file_address("127.0.0.1:47613".parse().expect("an address"))
        .expect("the address clean server binds writes the default file");

    let dir = tempfile::tempdir().expect("scratch");
    let path = dir.path().join("server.token");
    crate::announce_token(
        Some(&TokenFile::At(path.clone())),
        "[::1]:47613".parse().expect("an address"),
        &token(),
    )
    .expect("a named file is written whatever the address");
    assert_eq!(
        fs::read_to_string(&path).expect("read"),
        format!("{TOKEN}\n")
    );
}

#[test]
fn test_launch_banner_names_the_token_its_file_and_the_first_message() {
    let banner = launch_banner(
        &token(),
        Path::new("/run/clean/server-8080.token"),
        "127.0.0.1:8080".parse().expect("addr"),
    );
    assert_eq!(
        banner,
        format!(
            "clean-server: launch token {TOKEN} (also in /run/clean/server-8080.token, mode \
             0600); the first message on a connection to 127.0.0.1:8080 must be \
             {{\"jsonrpc\":\"2.0\",\"method\":\"authenticate\",\"params\":{{\"token\":\"{TOKEN}\"}},\
             \"id\":0}}"
        )
    );
}

// ── what a client presents ───────────────────────────────────────────────────

/// [`client_token_from`] over `vars` and a default token file in `dir`.
fn client(
    server: &str,
    vars: &HashMap<&str, OsString>,
    dir: &Path,
) -> Result<LaunchToken, ServerError> {
    client_token_from(
        server,
        |name| vars.get(name).cloned(),
        |port| Ok(dir.join(format!("server-{port}.token"))),
    )
}

#[test]
fn test_client_token_reads_the_variable_then_the_named_file_then_the_default() {
    let dir = tempfile::tempdir().expect("scratch");
    let other = "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100";
    fs::write(dir.path().join("server-8080.token"), format!("{TOKEN}\n")).expect("default");
    let named = dir.path().join("named.token");
    fs::write(&named, other).expect("named");

    let mut vars = HashMap::new();
    let found = client("127.0.0.1:8080", &vars, dir.path()).expect("the default file");
    assert_eq!(found.as_str(), TOKEN);

    vars.insert(CLIENT_TOKEN_FILE_ENV, named.clone().into_os_string());
    let found = client("127.0.0.1:8080", &vars, dir.path()).expect("the named file");
    assert_eq!(found.as_str(), other);

    vars.insert(CLIENT_TOKEN_ENV, OsString::from(TOKEN));
    let found = client("127.0.0.1:8080", &vars, dir.path()).expect("the variable");
    assert_eq!(found.as_str(), TOKEN);
}

#[test]
fn test_client_token_names_why_it_has_none() {
    let dir = tempfile::tempdir().expect("scratch");
    let mut vars = HashMap::new();
    let missing = dir.path().join("server-9.token");
    let error = client("127.0.0.1:9", &vars, dir.path()).expect_err("no token file");
    assert!(
        error.to_string().starts_with(&format!(
            "token file `{}`: cannot read the launch token (",
            missing.display()
        )),
        "{error}"
    );
    assert!(
        error.to_string().ends_with(
            "); set CLEAN_SERVER_TOKEN or CLEAN_SERVER_TOKEN_FILE, or start the server with its \
             default token file"
        ),
        "{error}"
    );

    let error = client("localhost", &vars, dir.path()).expect_err("no port");
    assert_eq!(
        error.to_string(),
        "launch token: `localhost` names no port, so the default token file is unknown; set \
         CLEAN_SERVER_TOKEN or CLEAN_SERVER_TOKEN_FILE"
    );

    vars.insert(CLIENT_TOKEN_ENV, OsString::from("abc"));
    let error = client("127.0.0.1:9", &vars, dir.path()).expect_err("not a token");
    assert_eq!(
        error.to_string(),
        "launch token: CLEAN_SERVER_TOKEN is not a launch token: expected 64 hex digits, found 3 \
         characters"
    );
}

/// The default file holds the token of the server on that port, which binds
/// `127.0.0.1` alone. Every other address may be another user's listener:
/// `::1` (where `localhost` resolves first on macOS) and the rest of 127/8 sit
/// beside the server on its port without conflict. The test this replaces
/// admitted `localhost`, `LocalHost`, `[::1]` and `127.1.2.3`, pinning the
/// leak as correct.
#[test]
fn test_client_token_sends_the_default_file_only_to_127_0_0_1() {
    let dir = tempfile::tempdir().expect("scratch");
    fs::write(dir.path().join("server-8080.token"), format!("{TOKEN}\n")).expect("default");
    let mut vars = HashMap::new();
    let found = client("127.0.0.1:8080", &vars, dir.path()).expect("the default file");
    assert_eq!(found.as_str(), TOKEN);
    for elsewhere in [
        "localhost:8080",
        "LocalHost:8080",
        "[::1]:8080",
        "[::ffff:127.0.0.1]:8080",
        "127.1.2.3:8080",
        "127.0.0.2:8080",
        "remote.example:8080",
        "10.0.0.1:8080",
        "[2001:db8::1]:8080",
        "localhost.attacker.example:8080",
    ] {
        let error = match client(elsewhere, &vars, dir.path()) {
            Ok(token) => panic!(
                "{elsewhere}: the client sent the default token file's token ({}) to an address \
                 the server that wrote it does not bind",
                token.as_str()
            ),
            Err(error) => error,
        };
        assert_eq!(
            error.to_string(),
            format!(
                "launch token: `{elsewhere}` is not 127.0.0.1, the one address `clean server` \
                 binds, so the default token file, which holds the token of the server there, is \
                 not sent to it; connect to 127.0.0.1:8080, or set CLEAN_SERVER_TOKEN or \
                 CLEAN_SERVER_TOKEN_FILE"
            )
        );
    }
    // A token the operator names goes where the operator sends it.
    let named = dir.path().join("named.token");
    fs::write(&named, TOKEN).expect("named");
    vars.insert(CLIENT_TOKEN_FILE_ENV, named.into_os_string());
    for server in ["remote.example:8080", "[::1]:8080"] {
        let found = client(server, &vars, dir.path()).expect("the named file");
        assert_eq!(found.as_str(), TOKEN, "{server}");
    }
}

/// A client asked for `localhost` connects to `127.0.0.1`, where the server
/// is, and so presents the default file's token there; nothing else is
/// rewritten.
#[test]
fn test_client_address_connects_localhost_to_127_0_0_1_only() {
    for (server, address) in [
        ("localhost:8080", "127.0.0.1:8080"),
        ("LOCALHOST:8080", "127.0.0.1:8080"),
        ("127.0.0.1:8080", "127.0.0.1:8080"),
        ("[::1]:8080", "[::1]:8080"),
        ("127.1.2.3:8080", "127.1.2.3:8080"),
        ("localhost", "localhost"),
        ("localhost:http", "localhost:http"),
        (
            "localhost.attacker.example:8080",
            "localhost.attacker.example:8080",
        ),
        ("remote.example:8080", "remote.example:8080"),
    ] {
        assert_eq!(client_address(server), address, "{server}");
    }
    let dir = tempfile::tempdir().expect("scratch");
    fs::write(dir.path().join("server-8080.token"), format!("{TOKEN}\n")).expect("default");
    let found = client(
        &client_address("localhost:8080"),
        &HashMap::new(),
        dir.path(),
    )
    .expect("`localhost` is connected as 127.0.0.1, which the default file is sent to");
    assert_eq!(found.as_str(), TOKEN);
}
