//! The bounded native-entry contract. These records are compiler observations,
//! not authority: the owner also binds this driver, actual argv and artifact,
//! source scanner verdict, SDK books and the complete unfiltered test run.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, Metadata};
use std::io::Read;
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path, PathBuf};
use std::sync::OnceLock;

use rustc_attr_ir::{Attribute, AttributeKind};
use rustc_hir as hir;
use rustc_hir::def::{DefKind, Res};
use rustc_interface::interface::Compiler;
use rustc_middle::middle::trust_test_harness::{
    test_harness_markers_are_all_builtin, test_harness_synthesized_item, TestHarnessItem,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};
use rustc_span::def_id::{CrateNum, DefId, LocalDefId, LOCAL_CRATE};
use rustc_span::{FileName, SourceFileHash, SourceFileHashAlgorithm};

const CONTEXT_PATH: &str = "CLEAN_LINT_TYPES_NATIVE_ENTRY_CONTEXT";
const CONTEXT_HASH: &str = "CLEAN_LINT_TYPES_NATIVE_ENTRY_CONTEXT_SHA256";
const CALLBACK: &str = "lint_types_native_test_entry";
const CONTEXT_LIMIT: u64 = 4 * 1024 * 1024;
#[cfg(not(test))]
const MANIFEST_LIMIT: u64 = 2 * 1024 * 1024;
#[cfg(not(test))]
const CONTEXT_KEYS: &[&str] = &[
    "compiler",
    "crate_name",
    "nonce",
    "out_dir_root",
    "role",
    "root",
    "schema",
    "sdk_manifest_identity",
    "sdk_manifest_path",
    "sdk_manifest_sha256",
    "sdk_root",
    "source",
    "source_sha256",
];

// This is the complete original Source roster, not a hand-written runner list.
// It authenticates what the compiler's real generated descriptor slice contains.
const TEST_NAMES: &[&str] = &[
    "tests::a_whole_arm_catch_all_beside_a_variant_is_refused",
    "tests::a_catch_all_below_the_top_is_refused",
    "tests::a_named_constant_is_the_variants_it_denotes",
    "tests::a_binding_is_a_binding_whatever_its_case",
    "tests::self_and_an_alias_are_the_type_they_name",
    "tests::a_refutable_let_has_a_catch_all_failure_branch",
    "tests::a_match_a_macro_writes_is_scanned",
    "tests::every_body_is_scanned",
    "tests::a_guard_does_not_make_a_catch_all_safe",
    "tests::named_variants_and_ungated_catch_alls_pass",
    "tests::a_comparison_with_a_named_variant_is_refused",
    "tests::a_named_variant_is_followed_through_bindings",
    "tests::a_named_variant_is_followed_into_closures_and_calls",
    "tests::a_value_of_a_gated_enum_that_reads_no_variable_is_named",
    "tests::a_function_that_compares_what_it_is_given_is_a_comparison",
    "tests::a_named_variant_is_followed_into_the_crate_s_own_functions",
    "tests::a_named_variant_is_followed_out_of_the_crate_s_own_functions",
    "tests::a_named_variant_is_followed_into_callbacks_and_writes",
    "tests::a_bound_of_the_impl_or_the_resolved_impl_is_a_comparison",
    "tests::a_method_another_crate_runs_may_be_passed_any_value",
    "tests::an_impl_trait_result_may_hold_any_variant",
    "tests::a_comparison_of_a_type_parameter_may_tell_apart_any_variant",
    "tests::a_value_erased_to_a_trait_object_keeps_its_variants",
    "tests::a_comparison_passed_as_a_value_is_a_comparison",
    "tests::a_function_value_passed_on_is_called_with_what_the_callee_holds",
    "tests::a_discriminant_cast_is_refused",
    "tests::agreement_and_an_assertion_are_not_a_told_variant",
    "tests::trust_ir_s_enums_are_gated_and_no_other_crate_s",
    "tests::a_fixed_value_of_the_gated_crate_names_what_it_holds",
    "tests::an_incremental_rerun_scans_every_body_again",
];

struct ObjectBook {
    sha256: String,
    bytes: u64,
    mode: u32,
}

struct Context {
    fields: BTreeMap<String, Vec<u8>>,
    objects: BTreeMap<PathBuf, ObjectBook>,
    compiler_args: Vec<String>,
    unit_role: String,
    query_only: bool,
}

static CONTEXT: OnceLock<Context> = OnceLock::new();

pub(super) fn record_context_inputs(compiler: &Compiler) {
    for key in [CONTEXT_PATH, CONTEXT_HASH] {
        let value = std::env::var(key)
            .ok()
            .as_deref()
            .map(rustc_span::Symbol::intern);
        compiler
            .sess
            .env_depinfo
            .lock()
            .insert((rustc_span::Symbol::intern(key), value));
    }
}

fn refuse(why: impl Into<String>) -> String {
    format!("native-entry contract refused: {}", why.into())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        result.push(char::from(DIGITS[usize::from(byte >> 4)]));
        result.push(char::from(DIGITS[usize::from(byte & 15)]));
    }
    result
}

#[cfg(not(test))]
fn unhex(value: &str) -> Result<Vec<u8>, String> {
    if !value.len().is_multiple_of(2) {
        return Err(refuse("odd-length hex"));
    }
    fn digit(byte: u8) -> Result<u8, String> {
        match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            b'a'..=b'f' => Ok(byte - b'a' + 10),
            _ => Err(refuse("noncanonical hex")),
        }
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| Ok((digit(pair[0])? << 4) | digit(pair[1])?))
        .collect()
}

#[cfg(not(test))]
fn sha256(bytes: &[u8]) -> Vec<u8> {
    SourceFileHash::new_in_memory(SourceFileHashAlgorithm::Sha256, bytes)
        .hash_bytes()
        .to_vec()
}

fn json(fields: &BTreeMap<String, Vec<u8>>) -> String {
    let members: Vec<String> = fields
        .iter()
        .map(|(key, value)| format!("\"{key}\":\"{}\"", hex(value)))
        .collect();
    format!("{{{}}}", members.join(","))
}

#[cfg(not(test))]
fn context_json(raw: &[u8]) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let text = std::str::from_utf8(raw).map_err(|_| refuse("context is not UTF8"))?;
    let inner = text
        .strip_prefix('{')
        .and_then(|s| s.strip_suffix('}'))
        .ok_or_else(|| refuse("context object framing"))?;
    let mut fields = BTreeMap::new();
    for member in inner.split(',') {
        let (key, value) = member
            .split_once(':')
            .ok_or_else(|| refuse("context member"))?;
        let key = key
            .strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .ok_or_else(|| refuse("context key"))?;
        if !CONTEXT_KEYS.contains(&key) {
            return Err(refuse("unknown context key"));
        }
        let value = value
            .strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'))
            .ok_or_else(|| refuse("context value must be hex string"))?;
        if fields.insert(key.to_string(), unhex(value)?).is_some() {
            return Err(refuse("duplicate context key"));
        }
    }
    if fields.len() != CONTEXT_KEYS.len() || json(&fields).as_bytes() != raw {
        return Err(refuse("missing/noncanonical context members"));
    }
    Ok(fields)
}

fn text<'a>(fields: &'a BTreeMap<String, Vec<u8>>, key: &str) -> Result<&'a str, String> {
    let value = fields
        .get(key)
        .ok_or_else(|| refuse(format!("missing {key}")))?;
    std::str::from_utf8(value).map_err(|_| refuse(format!("{key} is not UTF8")))
}

fn absolute(path: &Path) -> Result<(), String> {
    if !path.is_absolute() || path.components().any(|part| !matches_component(part)) {
        return Err(refuse("path is not absolute with normal components"));
    }
    Ok(())
}

fn matches_component(part: Component<'_>) -> bool {
    match part {
        Component::RootDir | Component::Normal(_) => true,
        Component::Prefix(_) | Component::CurDir | Component::ParentDir => false,
    }
}

fn ordinary_path(path: &Path) -> Result<(), String> {
    absolute(path)?;
    let mut prefix = PathBuf::new();
    for part in path.components() {
        prefix.push(part.as_os_str());
        let meta = fs::symlink_metadata(&prefix).map_err(|error| refuse(error.to_string()))?;
        if meta.file_type().is_symlink() {
            return Err(refuse("path contains a symlink"));
        }
        if prefix != path && !meta.is_dir() {
            return Err(refuse("path ancestor is not directory"));
        }
    }
    if fs::canonicalize(path).map_err(|error| refuse(error.to_string()))? != path {
        return Err(refuse("aliased path"));
    }
    Ok(())
}

// The public compiler may query its version before Cargo initializes this
// target. Validate every existing ancestor without creating a path or marker.
#[cfg(not(test))]
fn prospective_directory(path: &Path) -> Result<(), String> {
    absolute(path)?;
    let mut prefix = PathBuf::new();
    for part in path.components() {
        prefix.push(part.as_os_str());
        match fs::symlink_metadata(&prefix) {
            Ok(meta) => {
                if !meta.is_dir() || meta.file_type().is_symlink() {
                    return Err(refuse("prospective target has nonordinary ancestor"));
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(error) => return Err(refuse(error.to_string())),
        }
    }
    Ok(())
}

fn same_file(left: &Metadata, right: &Metadata) -> bool {
    left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.len() == right.len()
        && left.mode() == right.mode()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
        && left.nlink() == right.nlink()
}

fn opened(path: &Path) -> Result<(File, Metadata), String> {
    ordinary_path(path)?;
    let before = fs::symlink_metadata(path).map_err(|error| refuse(error.to_string()))?;
    if !before.is_file() {
        return Err(refuse("expected ordinary file"));
    }
    let file = File::open(path).map_err(|error| refuse(error.to_string()))?;
    let actual = file.metadata().map_err(|error| refuse(error.to_string()))?;
    if !same_file(&before, &actual) {
        return Err(refuse("opened file identity changed"));
    }
    Ok((file, before))
}

fn stable(path: &Path, file: &File, before: &Metadata) -> Result<(), String> {
    ordinary_path(path)?;
    let after = fs::symlink_metadata(path).map_err(|error| refuse(error.to_string()))?;
    let actual = file.metadata().map_err(|error| refuse(error.to_string()))?;
    if !same_file(before, &after) || !same_file(before, &actual) {
        return Err(refuse("file changed while observed"));
    }
    Ok(())
}

fn read_file_with_identity(path: &Path, limit: u64) -> Result<(Vec<u8>, Metadata), String> {
    let (mut file, before) = opened(path)?;
    if before.len() > limit {
        return Err(refuse("file exceeds byte cap"));
    }
    let mut bytes = Vec::new();
    (&mut file)
        .take(limit + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| refuse(error.to_string()))?;
    if bytes.len() as u64 != before.len() {
        return Err(refuse("file length changed"));
    }
    let identity = file.metadata().map_err(|error| refuse(error.to_string()))?;
    if !same_file(&before, &identity) {
        return Err(refuse("opened file identity changed during read"));
    }
    stable(path, &file, &identity)?;
    Ok((bytes, identity))
}

fn read_file(path: &Path, limit: u64) -> Result<Vec<u8>, String> {
    read_file_with_identity(path, limit).map(|(bytes, _)| bytes)
}

#[cfg(not(test))]
fn manifest_identity(value: &str) -> Result<(u64, u64, u64, u32), String> {
    let parts: Vec<&str> = value.split(':').collect();
    if parts.len() != 4 {
        return Err(refuse("manifest identity fields"));
    }
    let device: u64 = parts[0].parse().map_err(|_| refuse("manifest device"))?;
    let inode: u64 = parts[1].parse().map_err(|_| refuse("manifest inode"))?;
    let bytes: u64 = parts[2]
        .parse()
        .map_err(|_| refuse("manifest byte count"))?;
    let mode = u32::from_str_radix(parts[3], 8).map_err(|_| refuse("manifest mode"))?;
    if device.to_string() != parts[0]
        || inode.to_string() != parts[1]
        || bytes.to_string() != parts[2]
        || format!("{mode:o}") != parts[3]
        || mode > 0o7777
    {
        return Err(refuse("noncanonical manifest identity"));
    }
    Ok((device, inode, bytes, mode))
}

#[cfg(not(test))]
fn object_books(raw: &[u8]) -> Result<BTreeMap<PathBuf, ObjectBook>, String> {
    if !raw.ends_with(b"\n") || raw.len() as u64 > MANIFEST_LIMIT {
        return Err(refuse("SDK object book framing/cap"));
    }
    let value = std::str::from_utf8(raw).map_err(|_| refuse("SDK manifest is not UTF8"))?;
    let body = value
        .strip_suffix('\n')
        .ok_or_else(|| refuse("SDK object book framing"))?;
    let mut books = BTreeMap::new();
    let mut previous: Option<&[u8]> = None;
    for line in body.split('\n') {
        let encoded = line.as_bytes();
        if previous.is_some_and(|last| encoded <= last) {
            return Err(refuse("SDK books are not strictly sorted"));
        }
        previous = Some(encoded);
        let parts: Vec<&str> = line.split('\t').collect();
        if parts.len() != 4 {
            return Err(refuse("SDK object book fields"));
        }
        let path_text = parts[0];
        if path_text.is_empty()
            || path_text.starts_with('/')
            || path_text
                .bytes()
                .any(|byte| byte == b'\t' || byte == b'\r' || byte == b'\n' || byte == 0)
            || path_text
                .split('/')
                .any(|part| part.is_empty() || part == "." || part == "..")
        {
            return Err(refuse("SDK relative path escapes root"));
        }
        let path = PathBuf::from(path_text);
        let digest = unhex(parts[1])?;
        let bytes: u64 = parts[2].parse().map_err(|_| refuse("SDK byte count"))?;
        let mode = u32::from_str_radix(parts[3], 8).map_err(|_| refuse("SDK mode"))?;
        if digest.len() != 32
            || bytes.to_string() != parts[2]
            || format!("{mode:o}") != parts[3]
            || mode > 0o7777
        {
            return Err(refuse("noncanonical SDK book"));
        }
        if books
            .insert(
                path,
                ObjectBook {
                    sha256: parts[1].to_string(),
                    bytes,
                    mode,
                },
            )
            .is_some()
        {
            return Err(refuse("duplicate SDK object path"));
        }
    }
    if books.is_empty() {
        return Err(refuse("empty SDK object books"));
    }
    Ok(books)
}

#[cfg(not(test))]
fn option_value<'a>(args: &'a [String], key: &str) -> Result<Option<&'a str>, String> {
    let mut result = None;
    for (index, arg) in args.iter().enumerate().skip(1) {
        let value = if arg == key {
            Some(
                args.get(index + 1)
                    .ok_or_else(|| refuse("missing option value"))?
                    .as_str(),
            )
        } else {
            arg.strip_prefix(&format!("{key}="))
        };
        if let Some(value) = value {
            if result.replace(value).is_some() {
                return Err(refuse("duplicate compiler option"));
            }
        }
    }
    Ok(result)
}

#[cfg(not(test))]
fn compiler_query(args: &[String]) -> bool {
    if args.len() == 2 && args[1] == "-vV" {
        return true;
    }
    let mut saw_print = false;
    let mut index = 1;
    while index < args.len() {
        let arg = args[index].as_str();
        if let Some(value) = arg.strip_prefix("--print=") {
            if ![
                "file-names",
                "sysroot",
                "target-libdir",
                "split-debuginfo",
                "crate-name",
                "cfg",
            ]
            .contains(&value)
            {
                return false;
            }
            saw_print = true;
        } else if arg == "--crate-name" {
            index += 1;
            if args.get(index).map(String::as_str) != Some("___") {
                return false;
            }
        } else if arg == "--crate-type" {
            index += 1;
            if !args.get(index).is_some_and(|value| {
                ["bin", "rlib", "dylib", "cdylib", "staticlib", "proc-macro"]
                    .contains(&value.as_str())
            }) {
                return false;
            }
        } else if arg == "-C" {
            index += 1;
            if args.get(index).map(String::as_str) != Some("panic=abort") {
                return false;
            }
        } else if arg == "-Z" {
            index += 1;
            if !args
                .get(index)
                .is_some_and(|value| ["trust-verify=off", "threads=1"].contains(&value.as_str()))
            {
                return false;
            }
        } else if arg == "-Ztrust-verify=off" || arg == "-Zthreads=1" {
            // The owner's unchanged hermetic compiler flags, not a new lane.
        } else if arg != "-" && arg != "-Wwarnings" {
            return false;
        }
        index += 1;
    }
    saw_print
}

/// Called only after the production entry's existing first capture. With no
/// contract declaration, ordinary wrapper/fixture behavior is unchanged.
#[cfg(not(test))]
pub(super) fn prepare(args: &mut Vec<String>) -> Result<bool, String> {
    let path = std::env::var_os(CONTEXT_PATH);
    let expected_hash = std::env::var_os(CONTEXT_HASH);
    let (path, expected_hash) = match (path, expected_hash) {
        (None, None) => return Ok(false),
        (Some(path), Some(hash)) => (
            PathBuf::from(
                path.into_string()
                    .map_err(|_| refuse("context path is not UTF8"))?,
            ),
            hash.into_string()
                .map_err(|_| refuse("context hash is not UTF8"))?,
        ),
        _ => return Err(refuse("context keys must occur together")),
    };
    let (raw, context_identity) = read_file_with_identity(&path, CONTEXT_LIMIT)?;
    if context_identity.mode() & 0o7777 != 0o600 {
        return Err(refuse("context input mode"));
    }
    if hex(&sha256(&raw)) != expected_hash {
        return Err(refuse("context hash mismatch"));
    }
    let fields = context_json(&raw)?;
    if text(&fields, "schema")? != "lint-types-native-entry-context-v2"
        || text(&fields, "crate_name")? != "lint_types"
        || !["actual-test-compile", "typed-analysis"].contains(&text(&fields, "role")?)
    {
        return Err(refuse("context schema/role/crate"));
    }
    for key in ["nonce", "source_sha256", "sdk_manifest_sha256"] {
        if fields.get(key).map(Vec::len) != Some(32) {
            return Err(refuse("context digest/nonce length"));
        }
    }
    if fields.get("source_sha256") != fields.get("source").map(|src| sha256(src)).as_ref() {
        return Err(refuse("context source hash"));
    }
    // Anchor input locations to the actual owned driver before args[0] is
    // rewritten to the selected compiler. Neither argv nor context names it.
    let executable = std::env::current_exe().map_err(|error| refuse(error.to_string()))?;
    ordinary_path(&executable)?;
    let parent = executable
        .parent()
        .ok_or_else(|| refuse("owned driver parent"))?;
    let nonce = fields.get("nonce").ok_or_else(|| refuse("missing nonce"))?;
    let directory = parent.join("native-entry-contexts").join(hex(nonce));
    ordinary_path(&directory)?;
    let directory_identity =
        fs::symlink_metadata(&directory).map_err(|error| refuse(error.to_string()))?;
    if !directory_identity.is_dir() || directory_identity.mode() & 0o7777 != 0o700 {
        return Err(refuse("nonce input directory mode/type"));
    }
    let manifest_path = Path::new(text(&fields, "sdk_manifest_path")?);
    let expected_context = directory.join("context.json");
    let expected_manifest = directory.join("sdk-objects.manifest");
    if path.as_os_str() != expected_context.as_os_str()
        || manifest_path.as_os_str() != expected_manifest.as_os_str()
    {
        return Err(refuse("nonce input path/basename"));
    }
    let declared_identity = manifest_identity(text(&fields, "sdk_manifest_identity")?)?;
    let context_bytes = u64::try_from(raw.len()).map_err(|_| refuse("context length overflow"))?;
    let remaining = CONTEXT_LIMIT
        .checked_sub(context_bytes)
        .ok_or_else(|| refuse("combined input byte cap"))?;
    let (manifest, actual_identity) =
        read_file_with_identity(manifest_path, MANIFEST_LIMIT.min(remaining))?;
    if actual_identity.mode() & 0o7777 != 0o600
        || declared_identity
            != (
                actual_identity.dev(),
                actual_identity.ino(),
                actual_identity.len(),
                actual_identity.mode() & 0o7777,
            )
    {
        return Err(refuse("manifest input identity/mode"));
    }
    if fields.get("sdk_manifest_sha256") != Some(&sha256(&manifest)) {
        return Err(refuse("SDK manifest hash"));
    }
    for key in ["root", "compiler", "sdk_root"] {
        ordinary_path(Path::new(text(&fields, key)?))?;
    }
    prospective_directory(Path::new(text(&fields, "out_dir_root")?))?;
    let objects = object_books(&manifest)?;
    let compiler = text(&fields, "compiler")?.to_string();
    // Context roles are wrapper roles of this exact selected compiler, never
    // acceptance of arbitrary configured wrappers or compiler-looking basenames.
    if args.get(1).map(String::as_str) != Some(compiler.as_str()) {
        return Err(refuse("wrapper compiler is not bound selected compiler"));
    }
    args.remove(1);
    args[0] = compiler.clone();
    let query_only = compiler_query(args);
    let test_flags = args.iter().filter(|arg| arg.as_str() == "--test").count();
    if test_flags > 1 {
        return Err(refuse("duplicate test-mode flag"));
    }
    let input_role = text(&fields, "role")?;
    let unit_role = if input_role == "actual-test-compile" {
        "actual-test-compile"
    } else if test_flags == 1 {
        "typed-test-analysis"
    } else {
        "typed-normal-analysis"
    }
    .to_string();
    if !query_only {
        if args.iter().any(|arg| arg.starts_with('@')) {
            return Err(refuse("response-file compiler argument"));
        }
        if option_value(args, "--crate-name")? != Some("lint_types") {
            return Err(refuse("wrong compilation crate"));
        }
        if input_role == "actual-test-compile" && test_flags != 1 {
            return Err(refuse("actual-test-compile role requires a test unit"));
        }
        let out = Path::new(
            option_value(args, "--out-dir")?
                .ok_or_else(|| refuse("missing owned output directory"))?,
        );
        ordinary_path(out)?;
        if !out.starts_with(Path::new(text(&fields, "out_dir_root")?)) {
            return Err(refuse("output outside owned target"));
        }
    }
    let context = Context {
        fields,
        objects,
        compiler_args: args.clone(),
        unit_role,
        query_only,
    };
    // The compiler executable itself must occur in the owner-bound SDK books.
    let _ = context.object(Path::new(&compiler))?;
    CONTEXT
        .set(context)
        .map_err(|_| refuse("duplicate driver context"))?;
    Ok(true)
}

impl Context {
    fn object(&self, path: &Path) -> Result<String, String> {
        let root = Path::new(text(&self.fields, "sdk_root")?);
        let relative = path
            .strip_prefix(root)
            .map_err(|_| refuse("resolved object outside SDK root"))?;
        let book = self
            .objects
            .get(relative)
            .ok_or_else(|| refuse("resolved object absent from SDK book"))?;
        let (mut file, before) = opened(path)?;
        if before.len() != book.bytes || before.mode() & 0o7777 != book.mode {
            return Err(refuse("resolved object size/mode mismatch"));
        }
        let digest = SourceFileHash::new(SourceFileHashAlgorithm::Sha256, &mut file)
            .map_err(|error| refuse(error.to_string()))?;
        stable(path, &file, &before)?;
        if hex(digest.hash_bytes()) != book.sha256 {
            return Err(refuse("resolved object digest mismatch"));
        }
        Ok(format!(
            "{}:{}:{}:{:o}:{}:{}",
            hex(path.as_os_str().as_encoded_bytes()),
            book.sha256,
            book.bytes,
            book.mode,
            before.dev(),
            before.ino()
        ))
    }
}

struct Facts<'a, 'tcx> {
    context: &'a Context,
    tcx: TyCtxt<'tcx>,
    values: BTreeMap<String, String>,
    crates: BTreeSet<CrateNum>,
}

impl Facts<'_, '_> {
    fn fact(&mut self, key: impl Into<String>, value: impl Into<String>) -> Result<(), String> {
        if self.values.insert(key.into(), value.into()).is_some() {
            return Err(refuse("duplicate resolved fact"));
        }
        Ok(())
    }

    fn crate_source(&mut self, cnum: CrateNum) -> Result<(), String> {
        if cnum == LOCAL_CRATE {
            return Err(refuse("SDK identity resolved locally"));
        }
        if !self.crates.insert(cnum) {
            return Ok(());
        }
        let source = self.tcx.used_crate_source(cnum);
        let prefix = format!("crate/{}/{}", cnum.as_u32(), self.tcx.crate_name(cnum));
        let mut present = 0;
        // Deliberately enumerate FOUR fields: CrateSource::paths omits the
        // sdylib interface and cannot establish this contract.
        for (slot, path) in [
            ("dylib", source.dylib.as_ref()),
            ("rlib", source.rlib.as_ref()),
            ("rmeta", source.rmeta.as_ref()),
            ("sdylib_interface", source.sdylib_interface.as_ref()),
        ] {
            let value = if let Some(path) = path {
                present += 1;
                self.context.object(path)?
            } else {
                "absent".to_string()
            };
            self.fact(format!("{prefix}/{slot}"), value)?;
        }
        if present == 0 {
            return Err(refuse("SDK crate has no selected source object"));
        }
        Ok(())
    }

    fn public_api(&self, cnum: CrateNum, path: &str, kind: DefKind) -> Result<DefId, String> {
        let (crate_name, remainder) = path
            .split_once("::")
            .ok_or_else(|| refuse("public SDK role path lacks crate"))?;
        if self.tcx.crate_name(cnum).as_str() != crate_name {
            return Err(refuse("public SDK role resolved in wrong crate"));
        }
        let names: Vec<&str> = remainder.split("::").collect();
        let mut parent = cnum.as_def_id();
        for (index, name) in names.iter().enumerate() {
            if name.is_empty() {
                return Err(refuse("empty public SDK path component"));
            }
            let wanted = if index + 1 == names.len() {
                kind
            } else if kind == DefKind::Variant && index + 2 == names.len() {
                DefKind::Enum
            } else {
                DefKind::Mod
            };
            let mut found = None;
            if self.tcx.def_kind(parent) == DefKind::Enum {
                if wanted != DefKind::Variant {
                    return Err(refuse("public SDK enum role is not a variant"));
                }
                for variant in self.tcx.adt_def(parent).variants() {
                    if variant.name.as_str() != *name {
                        continue;
                    }
                    if found.replace(variant.def_id).is_some() {
                        return Err(refuse("duplicate public SDK variant"));
                    }
                }
            } else {
                if self.tcx.def_kind(parent) != DefKind::Mod {
                    return Err(refuse("public SDK path owner is not a module"));
                }
                for child in self.tcx.module_children(parent) {
                    if child.ident.name.as_str() != *name || !child.vis.is_public() {
                        continue;
                    }
                    let Res::Def(actual_kind, target) = child.res else {
                        continue;
                    };
                    if actual_kind != wanted {
                        continue;
                    }
                    if found.replace(target).is_some() {
                        return Err(refuse("duplicate public SDK export"));
                    }
                }
            }
            parent = found.ok_or_else(|| refuse("missing exact public SDK export/kind"))?;
            if self.tcx.def_kind(parent) != wanted || parent.krate != cnum {
                return Err(refuse("public SDK export kind/crate differs"));
            }
        }
        Ok(parent)
    }

    fn identity(
        &mut self,
        label: &str,
        def: DefId,
        expected: &str,
        kind: DefKind,
    ) -> Result<(), String> {
        self.crate_source(def.krate)?;
        let public = self.public_api(def.krate, expected, kind)?;
        if def != public {
            return Err(refuse(format!(
                "wrong resolved identity for {label}: expected public {expected} ({public:?}), got {def:?}"
            )));
        }
        self.fact(
            label,
            format!("{def:?}\t{}\t{:?}", expected, self.tcx.def_path_hash(def)),
        )
    }
}

fn path_def(tck: &TypeckResults<'_>, expr: &hir::Expr<'_>) -> Result<DefId, String> {
    if let hir::ExprKind::Path(ref path) = expr.kind {
        if let Res::Def(_, def) = tck.qpath_res(path, expr.hir_id) {
            return Ok(def);
        }
    }
    Err(refuse("expected a directly resolved definition path"))
}

fn local_path(tck: &TypeckResults<'_>, expr: &hir::Expr<'_>, id: hir::HirId) -> bool {
    if let hir::ExprKind::Path(ref path) = expr.kind {
        if let Res::Local(actual) = tck.qpath_res(path, expr.hir_id) {
            return actual == id;
        }
    }
    false
}

fn block<'a>(expr: &'a hir::Expr<'a>) -> Result<&'a hir::Block<'a>, String> {
    if let hir::ExprKind::Block(block, None) = expr.kind {
        return Ok(block);
    }
    Err(refuse("expected plain compiler block"))
}

fn stmt_expr<'a>(stmt: &'a hir::Stmt<'a>) -> Result<&'a hir::Expr<'a>, String> {
    match stmt.kind {
        hir::StmtKind::Expr(expr) | hir::StmtKind::Semi(expr) => Ok(expr),
        hir::StmtKind::Let(_) | hir::StmtKind::Item(_) => {
            Err(refuse("expected expression statement"))
        }
    }
}

fn call<'a>(expr: &'a hir::Expr<'a>) -> Result<(&'a hir::Expr<'a>, &'a [hir::Expr<'a>]), String> {
    if let hir::ExprKind::Call(callee, args) = expr.kind {
        return Ok((callee, args));
    }
    Err(refuse("expected direct call"))
}

fn peel<'a>(mut expr: &'a hir::Expr<'a>) -> &'a hir::Expr<'a> {
    loop {
        match expr.kind {
            hir::ExprKind::DropTemps(inner) => expr = inner,
            hir::ExprKind::Block(inner, None) if inner.stmts.is_empty() => {
                if let Some(value) = inner.expr {
                    expr = value;
                } else {
                    return expr;
                }
            }
            hir::ExprKind::ConstBlock(_)
            | hir::ExprKind::Array(_)
            | hir::ExprKind::Call(..)
            | hir::ExprKind::MethodCall(..)
            | hir::ExprKind::Use(..)
            | hir::ExprKind::Tup(_)
            | hir::ExprKind::Binary(..)
            | hir::ExprKind::Unary(..)
            | hir::ExprKind::Lit(_)
            | hir::ExprKind::Cast(..)
            | hir::ExprKind::Type(..)
            | hir::ExprKind::Let(_)
            | hir::ExprKind::If(..)
            | hir::ExprKind::Loop(..)
            | hir::ExprKind::Match(..)
            | hir::ExprKind::Closure(_)
            | hir::ExprKind::Block(..)
            | hir::ExprKind::Assign(..)
            | hir::ExprKind::AssignOp(..)
            | hir::ExprKind::Field(..)
            | hir::ExprKind::Index(..)
            | hir::ExprKind::Path(_)
            | hir::ExprKind::AddrOf(..)
            | hir::ExprKind::Break(..)
            | hir::ExprKind::Continue(_)
            | hir::ExprKind::Ret(_)
            | hir::ExprKind::Become(_)
            | hir::ExprKind::InlineAsm(_)
            | hir::ExprKind::OffsetOf(..)
            | hir::ExprKind::Struct(..)
            | hir::ExprKind::Repeat(..)
            | hir::ExprKind::Yield(..)
            | hir::ExprKind::UnsafeBinderCast(..)
            | hir::ExprKind::Err(_) => return expr,
        }
    }
}

fn binding(pat: &hir::Pat<'_>, name: &str) -> Result<hir::HirId, String> {
    if let hir::PatKind::Binding(mode, id, ident, None) = pat.kind {
        if mode == rustc_ast::BindingMode::NONE && ident.name.as_str() == name {
            return Ok(id);
        }
    }
    Err(refuse(format!("expected single {name} binding")))
}

fn let_stmt<'a>(
    stmt: &'a hir::Stmt<'a>,
    name: &str,
) -> Result<(hir::HirId, &'a hir::Expr<'a>), String> {
    if let hir::StmtKind::Let(local) = stmt.kind {
        if local.ty.is_none() && local.els.is_none() {
            return Ok((
                binding(local.pat, name)?,
                local.init.ok_or_else(|| refuse("missing initializer"))?,
            ));
        }
    }
    Err(refuse("expected canonical local initializer"))
}

fn adt(ty: Ty<'_>) -> Result<DefId, String> {
    if let ty::Adt(def, _) = ty.kind() {
        return Ok(def.did());
    }
    Err(refuse("expected actual SDK ADT"))
}

fn descriptor_type(ty: Ty<'_>) -> Result<DefId, String> {
    if let ty::Ref(_, slice, hir::Mutability::Not) = ty.kind() {
        if let ty::Slice(inner) = slice.kind() {
            if let ty::Ref(_, item, hir::Mutability::Not) = inner.kind() {
                return adt(*item);
            }
        }
    }
    Err(refuse(
        "callback parameter is not immutable descriptor slice",
    ))
}

fn marker(tcx: TyCtxt<'_>, def: LocalDefId) -> Result<String, String> {
    let mut name = None;
    for attr in tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)) {
        if let Attribute::Parsed(AttributeKind::RustcTestMarker(symbol)) = attr {
            if name.replace(symbol.as_str().to_string()).is_some() {
                return Err(refuse("duplicate test marker"));
            }
        }
    }
    name.ok_or_else(|| refuse("descriptor has no actual test marker"))
}

fn entry<'tcx>(facts: &mut Facts<'_, 'tcx>, callback: LocalDefId) -> Result<(), String> {
    let tcx = facts.tcx;
    if !test_harness_markers_are_all_builtin(tcx) {
        return Err(refuse("nonbuiltin test marker"));
    }
    let (main, _) = tcx
        .entry_fn(())
        .ok_or_else(|| refuse("missing compiler entry"))?;
    let main_local = main
        .as_local()
        .ok_or_else(|| refuse("nonlocal harness entry"))?;
    if test_harness_synthesized_item(tcx, main_local) != Some(TestHarnessItem::HarnessMain) {
        return Err(refuse("entry lacks SDK harness provenance"));
    }
    facts.fact("entry", format!("{main:?}"))?;
    let main_body = tcx.hir_body_owned_by(main_local);
    let main_block = block(main_body.value)?;
    if !main_body.params.is_empty() {
        return Err(refuse("generated main has unexpected body"));
    }
    // The harness builder emits one AST StmtKind::Expr. AST lowering promotes
    // a final expression to Block.expr; retain the equivalent single-statement
    // form as well, without accepting any additional operation.
    let invocation = match (main_block.stmts, main_block.expr) {
        ([], Some(expr)) => expr,
        ([stmt], None) => stmt_expr(stmt)?,
        _ => {
            return Err(refuse(
                "generated main has more than its one callback invocation",
            ))
        }
    };
    let (callee, args) = call(invocation)?;
    let tck = tcx.typeck(main_local);
    if path_def(tck, callee)? != callback.to_def_id() || args.len() != 1 {
        return Err(refuse("generated main does not call exact callback"));
    }
    let array = match args[0].kind {
        hir::ExprKind::AddrOf(_, hir::Mutability::Not, value) => value,
        hir::ExprKind::ConstBlock(_)
        | hir::ExprKind::Array(_)
        | hir::ExprKind::Call(..)
        | hir::ExprKind::MethodCall(..)
        | hir::ExprKind::Use(..)
        | hir::ExprKind::Tup(_)
        | hir::ExprKind::Binary(..)
        | hir::ExprKind::Unary(..)
        | hir::ExprKind::Lit(_)
        | hir::ExprKind::Cast(..)
        | hir::ExprKind::Type(..)
        | hir::ExprKind::DropTemps(_)
        | hir::ExprKind::Let(_)
        | hir::ExprKind::If(..)
        | hir::ExprKind::Loop(..)
        | hir::ExprKind::Match(..)
        | hir::ExprKind::Closure(_)
        | hir::ExprKind::Block(..)
        | hir::ExprKind::Assign(..)
        | hir::ExprKind::AssignOp(..)
        | hir::ExprKind::Field(..)
        | hir::ExprKind::Index(..)
        | hir::ExprKind::Path(_)
        | hir::ExprKind::AddrOf(..)
        | hir::ExprKind::Break(..)
        | hir::ExprKind::Continue(_)
        | hir::ExprKind::Ret(_)
        | hir::ExprKind::Become(_)
        | hir::ExprKind::InlineAsm(_)
        | hir::ExprKind::OffsetOf(..)
        | hir::ExprKind::Struct(..)
        | hir::ExprKind::Repeat(..)
        | hir::ExprKind::Yield(..)
        | hir::ExprKind::UnsafeBinderCast(..)
        | hir::ExprKind::Err(_) => {
            return Err(refuse("generated descriptor slice is not immutable borrow"))
        }
    };
    let members = if let hir::ExprKind::Array(members) = array.kind {
        members
    } else {
        return Err(refuse(
            "generated descriptor slice is not full literal array",
        ));
    };
    if members.len() != TEST_NAMES.len() {
        return Err(refuse("generated descriptor count differs from thirty"));
    }
    let expected: BTreeSet<&str> = TEST_NAMES.iter().copied().collect();
    let mut actual = BTreeSet::new();
    let mut ids = BTreeSet::new();
    let mut previous = String::new();
    for member in members {
        let member = match member.kind {
            hir::ExprKind::AddrOf(_, hir::Mutability::Not, value) => value,
            hir::ExprKind::ConstBlock(_)
            | hir::ExprKind::Array(_)
            | hir::ExprKind::Call(..)
            | hir::ExprKind::MethodCall(..)
            | hir::ExprKind::Use(..)
            | hir::ExprKind::Tup(_)
            | hir::ExprKind::Binary(..)
            | hir::ExprKind::Unary(..)
            | hir::ExprKind::Lit(_)
            | hir::ExprKind::Cast(..)
            | hir::ExprKind::Type(..)
            | hir::ExprKind::DropTemps(_)
            | hir::ExprKind::Let(_)
            | hir::ExprKind::If(..)
            | hir::ExprKind::Loop(..)
            | hir::ExprKind::Match(..)
            | hir::ExprKind::Closure(_)
            | hir::ExprKind::Block(..)
            | hir::ExprKind::Assign(..)
            | hir::ExprKind::AssignOp(..)
            | hir::ExprKind::Field(..)
            | hir::ExprKind::Index(..)
            | hir::ExprKind::Path(_)
            | hir::ExprKind::AddrOf(..)
            | hir::ExprKind::Break(..)
            | hir::ExprKind::Continue(_)
            | hir::ExprKind::Ret(_)
            | hir::ExprKind::Become(_)
            | hir::ExprKind::InlineAsm(_)
            | hir::ExprKind::OffsetOf(..)
            | hir::ExprKind::Struct(..)
            | hir::ExprKind::Repeat(..)
            | hir::ExprKind::Yield(..)
            | hir::ExprKind::UnsafeBinderCast(..)
            | hir::ExprKind::Err(_) => {
                return Err(refuse("descriptor element is not immutable borrow"))
            }
        };
        let def = path_def(tck, member)?
            .as_local()
            .ok_or_else(|| refuse("nonlocal descriptor"))?;
        if test_harness_synthesized_item(tcx, def) != Some(TestHarnessItem::TestDescriptorConst) {
            return Err(refuse("descriptor lacks actual builtin provenance"));
        }
        let name = marker(tcx, def)?;
        if name <= previous
            || !actual.insert(name.clone())
            || !ids.insert(def.local_def_index.as_u32())
        {
            return Err(refuse("unsorted/repeated descriptor"));
        }
        previous = name.clone();
        facts.fact(format!("descriptor/{name}"), format!("{def:?}\tbuiltin"))?;
    }
    if actual
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<&str>>()
        != expected
    {
        return Err(refuse("descriptor names differ from original thirty"));
    }
    let all_descriptors: BTreeSet<u32> = tcx
        .hir_crate_items(())
        .owners()
        .filter_map(|owner| {
            (test_harness_synthesized_item(tcx, owner.def_id)
                == Some(TestHarnessItem::TestDescriptorConst))
            .then_some(owner.def_id.local_def_index.as_u32())
        })
        .collect();
    if all_descriptors != ids {
        return Err(refuse("generated main omitted descriptor"));
    }
    facts.fact("descriptors/full-set", "30")?;
    Ok(())
}

fn callback<'tcx>(
    facts: &mut Facts<'_, 'tcx>,
    def: LocalDefId,
    test_crate: CrateNum,
) -> Result<(), String> {
    let tcx = facts.tcx;
    let body = tcx.hir_body_owned_by(def);
    let tck = tcx.typeck(def);
    if body.params.len() != 1 {
        return Err(refuse("callback parameter count"));
    }
    let parameter = binding(body.params[0].pat, "tests")?;
    let descriptor = descriptor_type(tck.pat_ty(body.params[0].pat))?;
    if descriptor.krate != test_crate {
        return Err(refuse("descriptor differs from actual test extern"));
    }
    facts.identity(
        "descriptor/type",
        descriptor,
        "test::TestDescAndFn",
        DefKind::Struct,
    )?;
    let code = block(body.value)?;
    if code.stmts.len() != 6 || code.expr.is_some() {
        return Err(refuse("callback body shape"));
    }
    let first = peel(stmt_expr(&code.stmts[0])?);
    let (condition, failure) = if let hir::ExprKind::If(condition, failure, None) = first.kind {
        (peel(condition), failure)
    } else {
        return Err(refuse("capture is not first guarded operation"));
    };
    let guard = if let hir::ExprKind::Let(guard) = condition.kind {
        guard
    } else {
        return Err(refuse("capture is not if-let"));
    };
    let (capture, capture_args) = call(peel(guard.init))?;
    if !capture_args.is_empty() {
        return Err(refuse("capture arguments"));
    }
    facts.identity(
        "capture",
        path_def(tck, capture)?,
        "rustc_data_structures::jobserver::capture_early_for_test_harness",
        DefKind::Fn,
    )?;
    let error_path = if let hir::PatKind::TupleStruct(ref path, pats, _) = guard.pat.kind {
        if pats.len() != 1 {
            return Err(refuse("Err payload count"));
        }
        let _ = binding(&pats[0], "error")?;
        path
    } else {
        return Err(refuse("failure guard is not actual Result::Err pattern"));
    };
    let error_def = if let Res::Def(_, def) = tck.qpath_res(error_path, guard.pat.hir_id) {
        def
    } else {
        return Err(refuse("unresolved Err pattern"));
    };
    let variant = match tcx.def_kind(error_def) {
        DefKind::Ctor(..) => tcx.parent(error_def),
        DefKind::Variant => error_def,
        DefKind::Mod
        | DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Trait
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::Fn
        | DefKind::Const
        | DefKind::ConstParam
        | DefKind::Static { .. }
        | DefKind::AssocFn
        | DefKind::AssocConst
        | DefKind::Macro(_)
        | DefKind::ExternCrate
        | DefKind::Use
        | DefKind::ForeignMod
        | DefKind::AnonConst
        | DefKind::OpaqueTy
        | DefKind::Field
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::Impl { .. }
        | DefKind::Closure
        | DefKind::SyntheticCoroutineBody
        | DefKind::TestBinderConstraints => {
            return Err(refuse("Err did not resolve to variant/constructor"))
        }
    };
    facts.identity(
        "failure/variant",
        variant,
        "core::result::Result::Err",
        DefKind::Variant,
    )?;
    facts.identity(
        "failure/enum",
        tcx.parent(variant),
        "core::result::Result",
        DefKind::Enum,
    )?;
    let failure = block(failure)?;
    if failure.stmts.len() != 2 || failure.expr.is_some() {
        return Err(refuse("capture failure body"));
    }
    let exit_call = stmt_expr(&failure.stmts[1])?;
    let (exit, exit_args) = call(exit_call)?;
    facts.identity(
        "failure/exit",
        path_def(tck, exit)?,
        "std::process::exit",
        DefKind::Fn,
    )?;
    if exit_args.len() != 1
        || tcx
            .sess
            .source_map()
            .span_to_snippet(exit_args[0].span)
            .map_err(|_| refuse("exit code source unavailable"))?
            != "75"
        || !tck.expr_ty(exit_call).is_never()
    {
        return Err(refuse("failure does not diverge with actual code75"));
    }
    let (_, policy) = let_stmt(&code.stmts[1], "sdk_loan")?;
    let (policy, policy_args) = call(policy)?;
    if !policy_args.is_empty() {
        return Err(refuse("SDK policy arguments"));
    }
    facts.identity(
        "policy/loan",
        path_def(tck, policy)?,
        "rustc_data_structures::jobserver::lends_own_execution",
        DefKind::Fn,
    )?;
    let (_, threads) = let_stmt(&code.stmts[2], "test_threads")?;
    let (threads, threads_args) = call(threads)?;
    if threads_args.len() != 1 {
        return Err(refuse("policy environment arguments"));
    }
    facts.identity(
        "policy/threads",
        path_def(tck, threads)?,
        "std::env::var_os",
        DefKind::Fn,
    )?;
    let (result, run) = let_stmt(&code.stmts[4], "result")?;
    let (runner, runner_args) = call(run)?;
    if runner_args.len() != 1 || !local_path(tck, &runner_args[0], parameter) {
        return Err(refuse(
            "libtest does not receive original immutable parameter",
        ));
    }
    let runner_def = path_def(tck, runner)?;
    if runner_def.krate != test_crate {
        return Err(refuse("runner differs from actual test extern"));
    }
    let expected_runner = if tcx.sess.panic_strategy().unwinds() {
        "test::test_main_env_args"
    } else {
        "test::test_main_env_args_abort"
    };
    facts.identity("libtest/runner", runner_def, expected_runner, DefKind::Fn)?;
    let exit_code = adt(tck.expr_ty(run))?;
    facts.identity(
        "libtest/result",
        exit_code,
        "std::process::ExitCode",
        DefKind::Struct,
    )?;
    let finish = stmt_expr(&code.stmts[5])?;
    let (receiver, args) = if let hir::ExprKind::MethodCall(_, receiver, args, _) = finish.kind {
        (receiver, args)
    } else {
        return Err(refuse("missing actual exit method"));
    };
    if !args.is_empty()
        || !local_path(tck, receiver, result)
        || adt(tck.expr_ty(receiver))? != exit_code
        || !tck.expr_ty(finish).is_never()
    {
        return Err(refuse(
            "libtest exit does not diverge using original ExitCode",
        ));
    }
    let method = tck
        .type_dependent_def_id(finish.hir_id)
        .ok_or_else(|| refuse("unresolved exit method"))?;
    let implementation = tcx
        .inherent_impl_of_assoc(method)
        .ok_or_else(|| refuse("exit is not an inherent SDK method"))?;
    let implementation_self = tcx
        .type_of(implementation)
        .instantiate_identity()
        .skip_norm_wip();
    if tcx.item_name(method).as_str() != "exit_process"
        || method.krate != exit_code.krate
        || adt(implementation_self)? != exit_code
    {
        return Err(refuse("exit is not genuine inherent SDK ExitCode method"));
    }
    facts.crate_source(method.krate)?;
    facts.fact(
        "libtest/exit",
        format!("{method:?}\t{}", tcx.def_path_str(method)),
    )?;
    facts.fact(
        "libtest/exit-impl",
        format!("{implementation:?}\t{exit_code:?}"),
    )?;
    facts.fact("callback", format!("{def:?}"))?;
    facts.fact("forwarded/parameter", format!("{parameter:?}"))?;
    Ok(())
}

/// Called from the existing real after_analysis callback. It does not replace
/// that callback, stop codegen, suppress diagnostics or substitute a re-analysis.
pub(super) fn check(compiler: &Compiler, tcx: TyCtxt<'_>) -> Result<(), String> {
    let candidates: Vec<LocalDefId> = tcx
        .hir_free_items()
        .filter_map(|id| {
            let item = tcx.hir_item(id);
            if let hir::ItemKind::Fn { ident, .. } = item.kind {
                (ident.name.as_str() == CALLBACK).then_some(item.owner_id.def_id)
            } else {
                None
            }
        })
        .collect();
    let Some(context) = CONTEXT.get() else {
        if !candidates.is_empty() {
            return Err(refuse("canonical entry lacks owner context"));
        }
        return Ok(());
    };
    if tcx.dcx().has_errors().is_some() {
        return Err(refuse("analysis already has emitted errors"));
    }
    if context.query_only {
        return Err(refuse("compiler query unexpectedly reached analysis"));
    }
    if tcx.crate_name(LOCAL_CRATE).as_str() != "lint_types" {
        return Err(refuse("analysis of wrong crate"));
    }
    let root = Path::new(text(&context.fields, "root")?);
    let input_path = if let rustc_session::config::Input::File(path) = &compiler.sess.io.input {
        path
    } else {
        return Err(refuse("actual unit is not filesystem root"));
    };
    let input = fs::canonicalize(input_path).map_err(|error| refuse(error.to_string()))?;
    if input != root {
        return Err(refuse("actual compiler root mismatch"));
    }
    let expected = context
        .fields
        .get("source")
        .ok_or_else(|| refuse("missing source"))?;
    if read_file(root, CONTEXT_LIMIT)? != *expected {
        return Err(refuse("root source bytes changed"));
    }
    let mut compiler_source = None;
    for file in compiler.sess.source_map().files().iter() {
        if let FileName::Real(name) = &file.name {
            if let Some(path) = name.local_path() {
                // Other imported SourceMap names may intentionally refer to
                // unavailable compiler sources. Do not touch those paths.
                if path == root || path == input_path {
                    if fs::canonicalize(path).map_err(|error| refuse(error.to_string()))? != root {
                        return Err(refuse("root SourceMap path mismatch"));
                    }
                    let src = file
                        .src
                        .as_ref()
                        .ok_or_else(|| refuse("root SourceMap buffer absent"))?;
                    if compiler_source.replace(src.as_bytes().to_vec()).is_some() {
                        return Err(refuse("duplicate root SourceMap buffers"));
                    }
                }
            }
        }
    }
    if compiler_source.as_ref() != Some(expected) {
        return Err(refuse("actual parsed source buffer differs"));
    }
    if compiler.sess.opts.sysroot.path() != Path::new(text(&context.fields, "sdk_root")?) {
        return Err(refuse("actual compiler sysroot mismatch"));
    }
    let mut facts = Facts {
        context,
        tcx,
        values: BTreeMap::new(),
        crates: BTreeSet::new(),
    };
    facts.fact(
        "compiler/book",
        context.object(Path::new(text(&context.fields, "compiler")?))?,
    )?;
    let wants_test = context.unit_role != "typed-normal-analysis";
    if tcx.sess.is_test_crate() != wants_test {
        return Err(refuse("actual analysis role mismatch"));
    }
    if wants_test {
        if candidates.len() != 1 {
            return Err(refuse("missing/duplicate canonical callback"));
        }
        let callback_id = candidates[0];
        let callback_def = callback_id.to_def_id();
        // Resolve exact root ownership and item identity. `def_path_str` is a
        // user-output formatter, not a canonical local definition identity.
        if tcx.parent(callback_def) != LOCAL_CRATE.as_def_id()
            || tcx.item_name(callback_def).as_str() != CALLBACK
        {
            return Err(refuse("callback is not exact root function"));
        }
        // Resolve the actual `extern crate test` declaration, rather than an
        // ident or search-directory candidate. All loaded defining crates below
        // are independently bound to their actual four-field CrateSource.
        let mut test_extern = None;
        for id in tcx.hir_free_items() {
            let item = tcx.hir_item(id);
            if let hir::ItemKind::ExternCrate(original, ident) = item.kind {
                // Each builtin #[test] expansion also introduces a hygienic
                // test extern. Select only the declared user ROOT extern;
                // nested generated imports are not competing declarations.
                if tcx.parent(item.owner_id.def_id.to_def_id()) == LOCAL_CRATE.as_def_id()
                    && ident.name.as_str() == "test"
                {
                    if original.is_some() || test_extern.is_some() {
                        return Err(refuse("renamed/duplicate test extern"));
                    }
                    test_extern = tcx.extern_mod_stmt_cnum(item.owner_id.def_id);
                }
            }
        }
        let test_extern = test_extern.ok_or_else(|| refuse("unresolved test extern"))?;
        if tcx.crate_name(test_extern).as_str() != "test" {
            return Err(refuse("test extern is wrong crate"));
        }
        facts.crate_source(test_extern)?;
        entry(&mut facts, callback_id)?;
        callback(&mut facts, callback_id, test_extern)?;
        let actual_crates: BTreeSet<String> = facts
            .crates
            .iter()
            .map(|cnum| tcx.crate_name(*cnum).as_str().to_string())
            .collect();
        let expected_crates: BTreeSet<String> = ["core", "std", "test", "rustc_data_structures"]
            .iter()
            .map(|name| name.to_string())
            .collect();
        if facts.crates.len() != 4 || actual_crates != expected_crates || facts.values.len() != 62 {
            return Err(refuse("entry resolved-fact/SDK role set is incomplete"));
        }
    } else {
        if !candidates.is_empty() {
            return Err(refuse("test callback in normal unit"));
        }
        facts.fact("unit", "normal-no-test-entry")?;
        if facts.values.len() != 2 {
            return Err(refuse("normal-unit fact set"));
        }
    }
    let mut record = BTreeMap::new();
    for key in [
        "nonce",
        "root",
        "source",
        "source_sha256",
        "sdk_root",
        "sdk_manifest_sha256",
    ] {
        record.insert(
            key.to_string(),
            context
                .fields
                .get(key)
                .ok_or_else(|| refuse("missing witness input"))?
                .clone(),
        );
    }
    record.insert(
        "context_role".to_string(),
        context
            .fields
            .get("role")
            .ok_or_else(|| refuse("missing context role"))?
            .clone(),
    );
    record.insert("role".to_string(), context.unit_role.as_bytes().to_vec());
    record.insert("schema".to_string(), b"lint-types-native-entry-v1".to_vec());
    let mut argv = Vec::new();
    for arg in &context.compiler_args {
        argv.extend_from_slice(arg.as_bytes());
        argv.push(0);
    }
    record.insert("compiler_argv".to_string(), argv);
    let mut resolved = String::new();
    for (key, value) in facts.values {
        resolved.push_str(&key);
        resolved.push('\t');
        resolved.push_str(&hex(value.as_bytes()));
        resolved.push('\n');
    }
    record.insert("resolved_facts".to_string(), resolved.into_bytes());
    eprintln!("lint-types-native-entry-v1 {}", json(&record));
    Ok(())
}
