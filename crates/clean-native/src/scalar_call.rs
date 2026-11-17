// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Experimental in-process `(UInt32, UInt32, UInt64, UInt64) -> UInt64` calls.
//!
//! Reuses source selection, the checked TrustIR/object lane, the complete C
//! runtime and the host dynamic loader. Lowered bodies remain explicitly
//! `clean-compiler-unvalidated`: this is no binary proof or product JIT permit.
//! The sole public constructor takes source, never an Environment, arbitrary
//! object path, code pointer, JSON record or hash pair. All managed values stay
//! inside the image. The handle is thread confined and calls require `&mut`.

use std::collections::{BTreeSet, HashSet};
use std::marker::PhantomData;
use std::path::Path;
use std::rc::Rc;

use anyhow::{bail, Context};
use clean_compiler::cli::{CompileArgs, EmitFormat};
use clean_compiler::emit_trust_ir_lane::{check_scalar_c_signature, defined_symbols, ScalarWord};
use clean_compiler::pass_manager::PipelineConfig;
use clean_compiler::Decl;
use clean_kernel::expr::UsedConstants;
use clean_kernel::{Environment, Expr, Name, TypeChecker};

mod observations;
use observations::ScalarSelectedInput;
pub use observations::{ObservedScalarCall, ObservedScalarCallFailure};

const ENTRY: &str = "clean_scalar_call";
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
type Entry = unsafe extern "C" fn(u32, u32, u64, u64) -> u64;

/// An owned loaded image with a checked fixed scalar prototype.
///
/// No callable pointer escapes this handle. Its scratch directory and runtime
/// remain alive until drop, which releases its loader reference before deleting
/// the files. The OS may keep an image mapped; no immediate-unmapping claim is
/// made.
/// Other native targets deliberately refuse until they execute qualification.
pub struct ScalarCall {
    image: loader::Image,
    root: Name,
    _scratch: tempfile::TempDir,
    _thread_confined: PhantomData<Rc<()>>,
}

impl ScalarCall {
    /// Compile an ordinary kernel-checked source through the existing native
    /// object lane, link its whole runtime, and load it once.
    ///
    /// # Errors
    /// Preserves selection/object/runtime/link refusals. Rejects other source
    /// types, noncanonical primitive closures and unsupported host ABIs before
    /// exposing a callable. The compiler remains an experimental trusted tool.
    pub fn from_source(file: &Path, declaration: &str, opt_level: u8) -> anyhow::Result<Self> {
        host()?;
        let args = CompileArgs {
            file: Some(file.to_path_buf()),
            decl: Some(declaration.to_owned()),
            emit: EmitFormat::Obj,
            opt_level,
            output: None,
            link_artifact: vec![],
        };
        let (decls, env, pipeline) = crate::compile::select_lcnf_decl(&args)?;
        let root = crate::compile::parse_compile_decl_name(declaration)?;
        Self::from_selected(&decls, &env, &pipeline, &root, Some(file), None)
    }

    /// Call the loaded body directly. Values cross only as these exact scalar
    /// widths; there is no subprocess, pointer marshalling or default result.
    pub fn call(&mut self, a: u32, b: u32, c: u64, d: u64) -> u64 {
        self.image.call(a, b, c, d)
    }

    /// The actual selected declaration whose body this handle compiled.
    /// This observation confers no separate binary proof authority.
    pub fn declaration(&self) -> &Name {
        &self.root
    }

    pub(crate) fn from_selected(
        decls: &[Decl],
        env: &Environment,
        pipeline: &PipelineConfig,
        root: &Name,
        source: Option<&Path>,
        closure: Option<&clean_compiler::RuntimeBindingClosure>,
    ) -> anyhow::Result<Self> {
        Self::from_selected_with_replay(decls, env, pipeline, root, source, closure, None)
    }

    pub(crate) fn from_selected_with_replay(
        decls: &[Decl],
        env: &Environment,
        pipeline: &PipelineConfig,
        root: &Name,
        source: Option<&Path>,
        closure: Option<&clean_compiler::RuntimeBindingClosure>,
        replay: Option<&clean_olean::ReplayedImportedSource>,
    ) -> anyhow::Result<Self> {
        Self::from_selected_input(
            ScalarSelectedInput::Borrowed {
                decls,
                env,
                pipeline,
                closure,
            },
            root,
            source,
            replay,
        )
    }

    fn from_selected_input(
        selected: ScalarSelectedInput<'_>,
        root: &Name,
        source: Option<&Path>,
        replay: Option<&clean_olean::ReplayedImportedSource>,
    ) -> anyhow::Result<Self> {
        let (decls, env, pipeline, closure) = selected.parts();
        host()?;
        source_contract_with_replay(env, root, replay)?;
        for declaration in decls {
            source_eligibility_with_replay(env, &declaration.name, replay)?;
        }
        let symbol = root.to_string();
        if symbol == ENTRY
            || !symbol
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b"_.$".contains(&b))
        {
            bail!("scalar entry symbol cannot be represented by the host C asm label: {symbol:?}");
        }
        let scratch = tempfile::tempdir().context("scalar callable scratch")?;
        let dir = scratch.path();
        crate::native_runtime::write_runtime_sources(dir)?;
        let runtime = crate::native_runtime::build_runtime_archive(
            dir,
            &crate::native_runtime::RuntimeMember::ALL,
        )?;
        if let ScalarSelectedInput::Observed { observer, .. } = selected {
            observer.runtime(&runtime);
        }
        let mut runtime_symbols = BTreeSet::new();
        for (_, path) in &runtime.objects {
            runtime_symbols.extend(object_symbols(path, false)?);
        }
        runtime_symbols.insert(ENTRY.to_owned());
        let object = dir.join("source.o");
        let check = |module: &clean_compiler::emit_trust_ir_lane::Module| {
            check_scalar_c_signature(
                module,
                &symbol,
                &[
                    ScalarWord::U32,
                    ScalarWord::U32,
                    ScalarWord::U64,
                    ScalarWord::U64,
                ],
                ScalarWord::U64,
            )
            .map_err(anyhow::Error::msg)?;
            // TrustIR's names are normative object link symbols. Refuse
            // source capture of actual runtime definitions OR imports
            // (such as malloc) before invoking codegen. Recheck the
            // emitted object's own definitions below as well.
            let mut names = defined_symbols(module);
            names.extend(module.globals.iter().map(|global| global.name.clone()));
            refuse_collisions(names.into_iter().collect(), &runtime_symbols)
        };
        match selected {
            ScalarSelectedInput::Borrowed { .. } => {
                crate::compile::emit_selected_object_with_check(
                    decls, env, pipeline, source, &object, closure, check,
                )?
            }
            ScalarSelectedInput::Observed { input, observer } => {
                crate::compile::emit_selected_object_owned_recording(
                    input, source, &object, observer, check,
                )?
            }
        }
        let source_symbols = object_symbols(&object, true)?;
        let source_all_symbols = object_symbols(&object, false)?;
        let source_imports: BTreeSet<_> = source_all_symbols
            .difference(&source_symbols)
            .cloned()
            .collect();
        if !source_symbols.contains(&symbol) {
            bail!("scalar object has no external definition of selected `{symbol}`");
        }
        refuse_collisions(source_symbols.clone(), &runtime_symbols)?;
        std::fs::write(
            dir.join("scalar-symbols.json"),
            serde_json::to_vec_pretty(
                &serde_json::json!({"source_definitions":source_symbols,"source_imports":source_imports,"runtime_definitions_and_imports":runtime_symbols,"claim":"actual symbol census only; no binary proof authority"}),
            )?,
        )?;
        let bridge = dir.join("scalar_bridge.c");
        std::fs::write(&bridge, format!(
            "#include <stdint.h>\n#include \"clean_runtime.h\"\n\
             extern uint64_t selected(uint32_t, uint32_t, uint64_t, uint64_t) __asm__(\"_{symbol}\");\n\
             __attribute__((constructor)) static void initialize(void) {{ clean_runtime_init(); }}\n\
             __attribute__((destructor)) static void finalize(void) {{ clean_runtime_finalize(); }}\n\
             uint64_t {ENTRY}(uint32_t a, uint32_t b, uint64_t c, uint64_t d) {{ return selected(a,b,c,d); }}\n"
        ))?;
        let library = dir.join("scalar.dylib");
        let output = crate::native_c_toolchain::command(&runtime.cc)?
            .args(["-dynamiclib", "-O2", "-std=c11", "-I"])
            .arg(dir)
            .arg(&bridge)
            .arg(&object)
            .args(runtime.objects.iter().map(|(_, path)| path))
            .args([
                "-lm",
                "-Wl,-undefined,error",
                "-Wl,-exported_symbol,_clean_scalar_call",
                "-o",
            ])
            .arg(&library)
            .output()
            .context("link scalar image with complete runtime")?;
        if !output.status.success() || !library.is_file() {
            bail!(
                "scalar image link refused ({}): {}",
                output.status,
                String::from_utf8_lossy(&output.stderr)
            );
        }
        if let ScalarSelectedInput::Observed { observer, .. } = selected {
            observer.file("actual linked scalar image", &library, None);
        }
        let image = loader::Image::open(&library)?;
        Ok(Self {
            image,
            root: root.clone(),
            _scratch: scratch,
            _thread_confined: PhantomData,
        })
    }
}

fn refuse_collisions(source: BTreeSet<String>, runtime: &BTreeSet<String>) -> anyhow::Result<()> {
    let conflicts: Vec<_> = source.intersection(runtime).collect();
    if !conflicts.is_empty() {
        bail!("source/runtime link symbol collision: {conflicts:?}");
    }
    Ok(())
}

fn object_symbols(path: &Path, defined_only: bool) -> anyhow::Result<BTreeSet<String>> {
    let mut command = std::process::Command::new("/usr/bin/nm");
    command.arg("-gj");
    if defined_only {
        command.arg("-U");
    }
    let output = command
        .arg(path)
        .output()
        .context("read actual Mach-O object symbols")?;
    if !output.status.success() {
        bail!(
            "scalar object symbol census refused for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let text = std::str::from_utf8(&output.stdout).context("object symbol census is not UTF-8")?;
    let mut symbols = BTreeSet::new();
    for line in text.lines().filter(|line| !line.is_empty()) {
        let symbol = line
            .strip_prefix('_')
            .filter(|name| !name.is_empty() && !name.chars().any(char::is_whitespace))
            .with_context(|| format!("malformed Mach-O symbol census row: {line:?}"))?;
        symbols.insert(symbol.to_owned());
    }
    if symbols.is_empty() {
        bail!("empty scalar object symbol census for {}", path.display());
    }
    Ok(symbols)
}

fn host() -> anyhow::Result<()> {
    if !cfg!(all(
        target_os = "macos",
        target_arch = "aarch64",
        target_endian = "little",
        target_pointer_width = "64"
    )) {
        bail!("scalar callable ABI is qualified only for aarch64-apple-darwin");
    }
    Ok(())
}

pub(crate) fn scalar_type() -> Expr {
    let u32_ty = Expr::const_str("UInt32");
    let u64_ty = Expr::const_str("UInt64");
    Expr::arrow(
        u32_ty.clone(),
        Expr::arrow(
            u32_ty,
            Expr::arrow(u64_ty.clone(), Expr::arrow(u64_ty.clone(), u64_ty)),
        ),
    )
}

#[cfg(test)]
fn source_contract(env: &Environment, root: &Name) -> anyhow::Result<()> {
    source_contract_with_replay(env, root, None)
}

fn source_contract_with_replay(
    env: &Environment,
    root: &Name,
    replay: Option<&clean_olean::ReplayedImportedSource>,
) -> anyhow::Result<()> {
    source_eligibility_with_replay(env, root, replay)?;
    // A name match is not a primitive/layout witness. Compare the complete
    // reachable kernel records and inductive/constructor/recursor roles with
    // Clean's own kernel-built canonical prelude, not caller-provided hashes.
    // This intentionally refuses a differing official/source representation;
    // extending that admission requires its own concrete layout controls.
    let canonical = Environment::try_with_prelude().context("canonical scalar prelude")?;
    let provenance = replay.map_or(env, |r| r.checked_environment());
    for name in scalar_dependencies(&canonical)? {
        if replay.is_some() {
            source_eligibility_with_replay(env, &name, replay)?;
        }
        let expected = canonical
            .get_const(&name)
            .with_context(|| format!("no canonical scalar dependency {name}"))?;
        if env.get_const(&name) != Some(expected)
            || env.get_inductive(&name) != canonical.get_inductive(&name)
            || env.get_constructor(&name) != canonical.get_constructor(&name)
            || env.get_recursor(&name) != canonical.get_recursor(&name)
            || env.get_structure_field_names(&name) != canonical.get_structure_field_names(&name)
            || env.get_structure_parents(&name) != canonical.get_structure_parents(&name)
            || provenance.declaration_verification(&name)
                != canonical.declaration_verification(&name)
            || env.get_extern(&name) != canonical.get_extern(&name)
            || env.get_implemented_by(&name) != canonical.get_implemented_by(&name)
            || env.is_unsafe(&name)
            || env.is_partial(&name)
            || env.is_staged_header(&name)
            || provenance.constant_needs_recheck(&name)
        {
            bail!("noncanonical scalar primitive/layout dependency `{name}`");
        }
    }
    let info = env
        .get_const(root)
        .context("selected scalar source declaration is absent")?;
    if !info.level_params.is_empty()
        || !TypeChecker::new(env).is_def_eq(&info.type_, &scalar_type())
    {
        bail!("scalar source type refused for `{root}`: expected UInt32 -> UInt32 -> UInt64 -> UInt64 -> UInt64");
    }
    Ok(())
}

pub(crate) fn scalar_source_roots() -> anyhow::Result<BTreeSet<Name>> {
    scalar_dependencies(&Environment::try_with_prelude().context("canonical scalar prelude")?)
}

fn scalar_dependencies(canonical: &Environment) -> anyhow::Result<BTreeSet<Name>> {
    let mut pending = vec![Name::from_string("UInt32"), Name::from_string("UInt64")];
    let mut seen = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let expected = canonical
            .get_const(&name)
            .with_context(|| format!("no canonical scalar dependency {name}"))?;
        let mut dependencies = HashSet::new();
        expected
            .type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut dependencies);
        if let Some(value) = &expected.value {
            value.used_constants_dag(UsedConstants::WithProjectionStructures, &mut dependencies);
        }
        if let Some(inductive) = canonical.get_inductive(&name) {
            dependencies.extend(inductive.constructor_names.iter().cloned());
            let recursor = name.clone().str("rec");
            if canonical.get_recursor(&recursor).is_some() {
                dependencies.insert(recursor);
            }
        }
        if let Some(fields) = canonical.get_structure_field_names(&name) {
            for field in fields {
                let projection = Name::append(&name, &field.to_string());
                if canonical.get_const(&projection).is_some() {
                    dependencies.insert(projection);
                }
            }
        }
        pending.extend(dependencies);
    }
    Ok(seen)
}

fn source_eligibility_with_replay(
    env: &Environment,
    name: &Name,
    replay: Option<&clean_olean::ReplayedImportedSource>,
) -> anyhow::Result<()> {
    let Some(replay) = replay else {
        return source_eligibility(env, name);
    };
    // Compiler-owned synthetic declarations retain the original policy. A
    // resident source declaration requires matching actual replay evidence.
    if env.get_const(name).is_none() {
        return source_eligibility(env, name);
    }
    replay.require_record(env, name)?;
    if env.is_unsafe(name) || env.is_partial(name) || env.is_staged_header(name) {
        bail!("scalar original source eligibility refused for `{name}`: unsafe, partial or staged declaration");
    }
    replay.checked_constant(name)?;
    source_eligibility(replay.checked_environment(), name)
}

fn source_eligibility(env: &Environment, name: &Name) -> anyhow::Result<()> {
    if env.is_unsafe(name)
        || env.is_partial(name)
        || env.is_staged_header(name)
        || env.constant_needs_recheck(name)
    {
        bail!("scalar source eligibility refused for `{name}`: unsafe, partial, staged or pending recheck declaration");
    }
    Ok(())
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod loader {
    use super::*;
    use std::ffi::{CStr, CString};
    use std::os::unix::ffi::OsStrExt;

    pub(super) struct Image {
        handle: *mut libc::c_void,
        entry: Entry,
    }

    fn error() -> String {
        // SAFETY: dlerror returns null or its own NUL-terminated diagnostic.
        unsafe {
            let p = libc::dlerror();
            if p.is_null() {
                "no loader diagnostic".into()
            } else {
                CStr::from_ptr(p).to_string_lossy().into_owned()
            }
        }
    }

    impl Image {
        pub(super) fn open(path: &Path) -> anyhow::Result<Self> {
            let path = CString::new(path.as_os_str().as_bytes())?;
            let symbol = CString::new(ENTRY)?;
            // SAFETY: the path is our just-linked private image. RTLD_NOW
            // refuses unresolved imports, LOCAL/FIRST confines symbol lookup.
            let handle = unsafe {
                libc::dlopen(
                    path.as_ptr(),
                    libc::RTLD_NOW | libc::RTLD_LOCAL | libc::RTLD_FIRST,
                )
            };
            if handle.is_null() {
                bail!("scalar image load refused: {}", error());
            }
            // SAFETY: handle is live and symbol is NUL-terminated. Its sole
            // exported wrapper was synthesized only after source+IR checks.
            let pointer = unsafe { libc::dlsym(handle, symbol.as_ptr()) };
            if pointer.is_null() {
                let reason = error();
                // SAFETY: release the successfully opened, unexposed image.
                unsafe {
                    libc::dlclose(handle);
                }
                bail!("scalar entry load refused: {reason}");
            }
            // SAFETY: this exact private wrapper has the literal fixed C
            // prototype Entry. Its callee's source and emitted prototype were
            // independently checked before compilation. No arbitrary pointer
            // or caller metadata reaches this conversion; handle owns lifetime.
            let entry = unsafe { std::mem::transmute::<*mut libc::c_void, Entry>(pointer) };
            Ok(Self { handle, entry })
        }
        pub(super) fn call(&mut self, a: u32, b: u32, c: u64, d: u64) -> u64 {
            // SAFETY: exact checked wrapper, live image, scalar inputs; &mut
            // plus thread confinement excludes concurrent/reentrant calls.
            unsafe { (self.entry)(a, b, c, d) }
        }
    }
    impl Drop for Image {
        fn drop(&mut self) {
            // SAFETY: Image uniquely owns this dlopen reference, and no code
            // pointer escapes. Calls borrow Image and finish before drop.
            unsafe {
                libc::dlclose(self.handle);
            }
        }
    }
}

#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
mod loader {
    use super::*;
    pub(super) struct Image;
    impl Image {
        pub(super) fn open(_: &Path) -> anyhow::Result<Self> {
            host()?;
            bail!("unsupported scalar loader")
        }
        pub(super) fn call(&mut self, _: u32, _: u32, _: u64, _: u64) -> u64 {
            unreachable!("unsupported host has no constructor")
        }
    }
}

#[cfg(test)]
mod tests;
