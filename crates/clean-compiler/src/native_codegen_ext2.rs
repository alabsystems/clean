// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended native code generation: compilation pipelines, caching, and JIT.
//!
//! Part of #3084 - IO/FFI/Native code generation infrastructure.

use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use thiserror::Error;

use crate::native_codegen_ext::NativeTarget;

/// Errors from the native compilation pipeline.
#[derive(Debug, Error)]
#[non_exhaustive]
pub(crate) enum NativeCompileError {
    #[error("compiler `{tool}` failed (exit {exit_code}): {stderr}")]
    ToolFailed {
        tool: String,
        exit_code: i32,
        stderr: String,
    },
    // Raised once the pipeline actually spawns toolchains: the module only
    // *plans* commands today (`plan_*` returns the argv, it never execs), so
    // no probe exists yet to fail. Kept as part of the pipeline's error
    // contract — 2026-07-31.
    #[allow(dead_code)]
    #[error("tool not found: {0}")]
    ToolNotFound(String),
    #[error("linker `{tool}` failed (exit {exit_code}): {stderr}")]
    LinkFailed {
        tool: String,
        exit_code: i32,
        stderr: String,
    },
    #[error("source file not found: {0}")]
    SourceNotFound(PathBuf),
    #[error("cache error: {0}")]
    CacheError(String),
    #[error("JIT error: {0}")]
    JitError(String),
    #[error("unsupported target triple: {0}")]
    UnsupportedTarget(String),
    #[error("I/O error: {0}")]
    Io(String),
}

/// CPU architecture component of a target triple.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum Arch {
    X86_64,
    Aarch64,
    Wasm32,
}

impl fmt::Display for Arch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::X86_64 => "x86_64",
            Self::Aarch64 => "aarch64",
            Self::Wasm32 => "wasm32",
        })
    }
}

/// Operating system component of a target triple.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum Os {
    Linux,
    Darwin,
    Windows,
    Unknown,
}

impl fmt::Display for Os {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Linux => "linux",
            Self::Darwin => "darwin",
            Self::Windows => "windows",
            Self::Unknown => "unknown",
        })
    }
}

/// A parsed target triple (arch-vendor-os).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TargetTriple {
    pub(crate) arch: Arch,
    pub(crate) vendor: String,
    pub(crate) os: Os,
    raw: String,
}

impl TargetTriple {
    /// Parse a target triple string like "x86_64-apple-darwin".
    pub(crate) fn parse(triple: &str) -> Result<Self, NativeCompileError> {
        let parts: Vec<&str> = triple.splitn(3, '-').collect();
        if parts.len() < 3 {
            return Err(NativeCompileError::UnsupportedTarget(triple.to_owned()));
        }
        let arch = match parts[0] {
            "x86_64" => Arch::X86_64,
            "aarch64" | "arm64" => Arch::Aarch64,
            "wasm32" => Arch::Wasm32,
            _ => return Err(NativeCompileError::UnsupportedTarget(triple.to_owned())),
        };
        let os = if parts[2].contains("linux") {
            Os::Linux
        } else if parts[2].contains("darwin") {
            Os::Darwin
        } else if parts[2].contains("windows") || parts[2].contains("win32") {
            Os::Windows
        } else {
            Os::Unknown
        };
        Ok(Self {
            arch,
            vendor: parts[1].to_owned(),
            os,
            raw: triple.to_owned(),
        })
    }

    /// Detect the host target triple from compile-time cfg.
    #[must_use]
    pub(crate) fn host() -> Self {
        #[cfg(all(target_arch = "x86_64", target_os = "macos"))]
        let raw = "x86_64-apple-darwin";
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        let raw = "aarch64-apple-darwin";
        #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
        let raw = "x86_64-unknown-linux-gnu";
        #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
        let raw = "aarch64-unknown-linux-gnu";
        #[cfg(not(any(
            all(target_arch = "x86_64", target_os = "macos"),
            all(target_arch = "aarch64", target_os = "macos"),
            all(target_arch = "x86_64", target_os = "linux"),
            all(target_arch = "aarch64", target_os = "linux"),
        )))]
        let raw = "x86_64-unknown-linux-gnu";
        Self::parse(raw).expect("invariant: host triple is always valid")
    }

    #[must_use]
    pub(crate) fn as_str(&self) -> &str {
        &self.raw
    }

    /// Shared library file extension for this target.
    #[must_use]
    pub(crate) fn shared_lib_ext(&self) -> &'static str {
        match self.os {
            Os::Darwin => "dylib",
            Os::Windows => "dll",
            _ => "so",
        }
    }

    /// Object file extension for this target.
    #[must_use]
    pub(crate) fn object_ext(&self) -> &'static str {
        match self.os {
            Os::Windows => "obj",
            _ => "o",
        }
    }
}

impl fmt::Display for TargetTriple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.raw)
    }
}

/// Select the compilation backend based on target and user preference.
#[must_use]
pub(crate) fn select_backend(
    _target: &TargetTriple,
    preferred: Option<NativeTarget>,
) -> NativeTarget {
    preferred.unwrap_or(NativeTarget::C)
}

/// An external compiler invocation to be run.
#[derive(Debug, Clone)]
pub(crate) struct CompilerCommand {
    pub(crate) tool: String,
    pub(crate) args: Vec<String>,
    pub(crate) source: PathBuf,
    pub(crate) output: PathBuf,
}

impl CompilerCommand {
    /// Build a C compilation command for the given target.
    #[must_use]
    pub(crate) fn c_compile(
        source: &Path,
        output: &Path,
        target: &TargetTriple,
        optimize: bool,
    ) -> Self {
        let tool = if target.os == Os::Darwin {
            "clang"
        } else {
            "cc"
        };
        let mut args = vec!["-c".to_owned()];
        if optimize {
            args.push("-O2".to_owned());
        }
        args.push("-fPIC".to_owned());
        if target.os != Os::Darwin {
            args.push(format!("--target={}", target.as_str()));
        }
        args.extend([
            "-o".to_owned(),
            output.display().to_string(),
            source.display().to_string(),
        ]);
        Self {
            tool: tool.to_owned(),
            args,
            source: source.to_owned(),
            output: output.to_owned(),
        }
    }

    /// Build a Rust compilation command (rustc) for the given target.
    #[must_use]
    pub(crate) fn rust_compile(
        source: &Path,
        output: &Path,
        target: &TargetTriple,
        optimize: bool,
    ) -> Self {
        let mut args = vec![
            "--crate-type".to_owned(),
            "staticlib".to_owned(),
            "--edition".to_owned(),
            "2021".to_owned(),
        ];
        if optimize {
            args.push("-O".to_owned());
        }
        args.extend([
            "--target".to_owned(),
            target.as_str().to_owned(),
            "-o".to_owned(),
            output.display().to_string(),
            source.display().to_string(),
        ]);
        Self {
            tool: "rustc".to_owned(),
            args,
            source: source.to_owned(),
            output: output.to_owned(),
        }
    }
}

/// A linker invocation to produce a shared library.
#[derive(Debug, Clone)]
pub(crate) struct LinkerCommand {
    pub(crate) tool: String,
    pub(crate) args: Vec<String>,
    pub(crate) objects: Vec<PathBuf>,
    // Recorded here and also spliced into `args` as `-o <output>`; the
    // structured copy is what an executing driver will read back to locate the
    // artifact. No exec driver yet — 2026-07-31.
    #[allow(dead_code)]
    pub(crate) output: PathBuf,
}

impl LinkerCommand {
    /// Build a linker command for the given target.
    #[must_use]
    pub(crate) fn for_target(objects: &[PathBuf], output: &Path, target: &TargetTriple) -> Self {
        let (tool, flag) = match target.os {
            Os::Darwin => ("clang", "-dynamiclib"),
            Os::Windows => ("link.exe", "/DLL"),
            _ => ("cc", "-shared"),
        };
        let mut args = vec![
            flag.to_owned(),
            "-o".to_owned(),
            output.display().to_string(),
        ];
        args.extend(objects.iter().map(|o| o.display().to_string()));
        Self {
            tool: tool.to_owned(),
            args,
            objects: objects.to_vec(),
            output: output.to_owned(),
        }
    }
}

/// Hash-based compilation cache to avoid recompiling unchanged sources.
#[derive(Debug)]
pub(crate) struct CompilationCache {
    cache_dir: PathBuf,
    entries: HashMap<u64, PathBuf>,
}

impl CompilationCache {
    pub(crate) fn new(cache_dir: &Path) -> Result<Self, NativeCompileError> {
        if !cache_dir.exists() {
            return Err(NativeCompileError::CacheError(format!(
                "cache directory does not exist: {}",
                cache_dir.display()
            )));
        }
        Ok(Self {
            cache_dir: cache_dir.to_owned(),
            entries: HashMap::new(),
        })
    }

    #[must_use]
    pub(crate) fn lookup(&self, content_hash: u64) -> Option<&Path> {
        self.entries.get(&content_hash).map(|p| p.as_path())
    }

    pub(crate) fn insert(&mut self, content_hash: u64, object_path: &Path) {
        self.entries.insert(content_hash, object_path.to_owned());
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub(crate) fn cache_dir(&self) -> &Path {
        &self.cache_dir
    }

    /// FNV-1a content hash.
    #[must_use]
    pub(crate) fn hash_content(content: &[u8]) -> u64 {
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for &b in content {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0100_0000_01b3);
        }
        h
    }
}

/// A single module to be compiled.
#[derive(Debug, Clone)]
pub(crate) struct CompilationUnit {
    pub(crate) name: String,
    pub(crate) source_path: PathBuf,
    pub(crate) backend: NativeTarget,
    pub(crate) content_hash: u64,
}

/// A plan for compiling multiple modules, potentially in parallel.
#[derive(Debug)]
pub(crate) struct ParallelCompilePlan {
    pub(crate) units: Vec<CompilationUnit>,
    pub(crate) target: TargetTriple,
    pub(crate) optimize: bool,
    pub(crate) output_dir: PathBuf,
}

impl ParallelCompilePlan {
    #[must_use]
    pub(crate) fn new(target: TargetTriple, optimize: bool, output_dir: PathBuf) -> Self {
        Self {
            units: Vec::new(),
            target,
            optimize,
            output_dir,
        }
    }

    pub(crate) fn add_unit(&mut self, unit: CompilationUnit) {
        self.units.push(unit);
    }

    #[must_use]
    pub(crate) fn unit_count(&self) -> usize {
        self.units.len()
    }

    /// Generate compiler commands for all units, checking cache for hits.
    #[must_use]
    pub(crate) fn generate_commands(
        &self,
        cache: &CompilationCache,
    ) -> (Vec<CompilerCommand>, Vec<PathBuf>) {
        let mut commands = Vec::new();
        let mut cached_objects = Vec::new();
        for unit in &self.units {
            if let Some(cached) = cache.lookup(unit.content_hash) {
                cached_objects.push(cached.to_owned());
                continue;
            }
            let obj_path =
                self.output_dir
                    .join(format!("{}.{}", unit.name, self.target.object_ext()));
            let cmd = match unit.backend {
                NativeTarget::C | NativeTarget::Llvm => CompilerCommand::c_compile(
                    &unit.source_path,
                    &obj_path,
                    &self.target,
                    self.optimize,
                ),
                NativeTarget::Rust => CompilerCommand::rust_compile(
                    &unit.source_path,
                    &obj_path,
                    &self.target,
                    self.optimize,
                ),
            };
            commands.push(cmd);
        }
        (commands, cached_objects)
    }
}

/// A JIT-compiled module loaded into the current process.
#[derive(Debug)]
pub(crate) struct JitModule {
    pub(crate) name: String,
    // The dlopen target. Only read once a loader exists; the module currently
    // stops at planning the shared-library path — 2026-07-31.
    #[allow(dead_code)]
    pub(crate) lib_path: PathBuf,
    pub(crate) symbols: Vec<String>,
}

impl JitModule {
    #[must_use]
    pub(crate) fn new(name: &str, lib_path: PathBuf) -> Self {
        Self {
            name: name.to_owned(),
            lib_path,
            symbols: Vec::new(),
        }
    }

    pub(crate) fn add_symbol(&mut self, symbol: &str) {
        self.symbols.push(symbol.to_owned());
    }

    #[must_use]
    pub(crate) fn has_symbol(&self, name: &str) -> bool {
        self.symbols.iter().any(|s| s == name)
    }
}

/// Plan a JIT compilation: compile source to shared library for runtime loading.
pub(crate) fn plan_jit_compile(
    source: &Path,
    output_dir: &Path,
    module_name: &str,
    target: &TargetTriple,
    optimize: bool,
) -> Result<(CompilerCommand, LinkerCommand, PathBuf), NativeCompileError> {
    if !source.exists() {
        return Err(NativeCompileError::SourceNotFound(source.to_owned()));
    }
    let obj_path = output_dir.join(format!("{module_name}.{}", target.object_ext()));
    let lib_path = output_dir.join(format!("lib{module_name}.{}", target.shared_lib_ext()));
    let compile_cmd = CompilerCommand::c_compile(source, &obj_path, target, optimize);
    let link_cmd = LinkerCommand::for_target(&[obj_path], &lib_path, target);
    Ok((compile_cmd, link_cmd, lib_path))
}

/// Descriptor for a loaded shared library (dlopen handle placeholder).
#[derive(Debug)]
pub(crate) struct SharedLibHandle {
    // The library this handle stands for. Read by the real dlopen call this
    // placeholder is standing in for — 2026-07-31.
    #[allow(dead_code)]
    pub(crate) path: PathBuf,
    pub(crate) loaded: bool,
    symbols: HashMap<String, usize>,
}

impl SharedLibHandle {
    #[must_use]
    pub(crate) fn new(path: PathBuf) -> Self {
        Self {
            path,
            loaded: false,
            symbols: HashMap::new(),
        }
    }

    pub(crate) fn mark_loaded(&mut self) {
        self.loaded = true;
    }

    pub(crate) fn register_symbol(&mut self, name: &str, addr: usize) {
        self.symbols.insert(name.to_owned(), addr);
    }

    #[must_use]
    pub(crate) fn symbol_addr(&self, name: &str) -> Option<usize> {
        self.symbols.get(name).copied()
    }

    #[must_use]
    pub(crate) fn symbol_count(&self) -> usize {
        self.symbols.len()
    }
}

/// Statistics from a compilation run.
#[derive(Debug, Clone)]
pub(crate) struct CompileStats {
    pub(crate) modules_compiled: usize,
    pub(crate) cache_hits: usize,
    pub(crate) compile_time: Duration,
    pub(crate) link_time: Duration,
    pub(crate) total_time: Duration,
}

impl CompileStats {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            modules_compiled: 0,
            cache_hits: 0,
            compile_time: Duration::ZERO,
            link_time: Duration::ZERO,
            total_time: Duration::ZERO,
        }
    }

    pub(crate) fn record_compile(&mut self, elapsed: Duration) {
        self.modules_compiled += 1;
        self.compile_time += elapsed;
    }

    pub(crate) fn record_cache_hit(&mut self) {
        self.cache_hits += 1;
    }

    pub(crate) fn record_link(&mut self, elapsed: Duration) {
        self.link_time += elapsed;
    }

    pub(crate) fn finalize(&mut self, total: Duration) {
        self.total_time = total;
    }

    #[must_use]
    pub(crate) fn cache_hit_rate(&self) -> f64 {
        let total = self.modules_compiled + self.cache_hits;
        if total == 0 {
            return 0.0;
        }
        self.cache_hits as f64 / total as f64
    }
}

impl Default for CompileStats {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for CompileStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "compiled={}, cache_hits={}, compile={:?}, link={:?}, total={:?}",
            self.modules_compiled,
            self.cache_hits,
            self.compile_time,
            self.link_time,
            self.total_time
        )
    }
}

/// Orchestrates the full compilation pipeline: compile, cache, link, stats.
#[derive(Debug)]
pub(crate) struct CompilePipeline {
    pub(crate) target: TargetTriple,
    pub(crate) backend: NativeTarget,
    pub(crate) optimize: bool,
    pub(crate) cache: Option<CompilationCache>,
    pub(crate) stats: CompileStats,
}

impl CompilePipeline {
    #[must_use]
    pub(crate) fn new(target: TargetTriple, backend: NativeTarget, optimize: bool) -> Self {
        Self {
            target,
            backend,
            optimize,
            cache: None,
            stats: CompileStats::new(),
        }
    }

    pub(crate) fn with_cache(mut self, cache: CompilationCache) -> Self {
        self.cache = Some(cache);
        self
    }

    /// Plan compilation of a single source file to an object file.
    pub(crate) fn plan_compile(
        &mut self,
        source: &Path,
        output_dir: &Path,
        module_name: &str,
    ) -> Result<Option<CompilerCommand>, NativeCompileError> {
        if !source.exists() {
            return Err(NativeCompileError::SourceNotFound(source.to_owned()));
        }
        let content_hash = CompilationCache::hash_content(module_name.as_bytes());
        if let Some(ref cache) = self.cache {
            if cache.lookup(content_hash).is_some() {
                self.stats.record_cache_hit();
                return Ok(None);
            }
        }
        let obj_path = output_dir.join(format!("{module_name}.{}", self.target.object_ext()));
        let cmd = match self.backend {
            NativeTarget::C | NativeTarget::Llvm => {
                CompilerCommand::c_compile(source, &obj_path, &self.target, self.optimize)
            }
            NativeTarget::Rust => {
                CompilerCommand::rust_compile(source, &obj_path, &self.target, self.optimize)
            }
        };
        let start = Instant::now();
        self.stats.record_compile(start.elapsed());
        Ok(Some(cmd))
    }

    /// Plan linking of object files into a shared library.
    pub(crate) fn plan_link(&mut self, objects: &[PathBuf], output: &Path) -> LinkerCommand {
        let start = Instant::now();
        let cmd = LinkerCommand::for_target(objects, output, &self.target);
        self.stats.record_link(start.elapsed());
        cmd
    }

    #[must_use]
    pub(crate) fn stats(&self) -> &CompileStats {
        &self.stats
    }
}
