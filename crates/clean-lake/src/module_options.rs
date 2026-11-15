// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `lean` arguments Lake compiles one module with (gap G50).
//!
//! Lake 4.8.0 compiles a `Module` (a name plus the `LeanLib` it was found
//! through) with `mod.weakLeanArgs ++ mod.leanArgs`
//! (`Lake/Build/Module.lean`), where for library `L` of package `P`
//!
//! - `weakLeanArgs` = `P.weakLeanArgs ++ L.weakLeanArgs`, and
//! - `leanArgs` = `P.leanOptions (as -D) ++ P.moreLeanArgs ++
//!   L.leanOptions (as -D) ++ L.moreLeanArgs` (`Lake/Config/LeanLib.lean`).
//!
//! `P` is the package that OWNS the module — a dependency's modules are
//! compiled with the dependency's own lakefile, never the root's. WHICH
//! library a module is compiled through depends on how the build reaches it:
//!
//! - a library target builds its roots through itself;
//! - an executable builds its root through `LeanExe.toLeanLib` (the package's
//!   arguments plus the executable's);
//! - an import is resolved by `Package.findModule?` =
//!   `leanLibs.findSomeRev? (·.findModule? mod)`: the LAST declared library
//!   whose `isBuildableModule` holds.
//!
//! Lake memoizes a module's build by name, so when those routes disagree the
//! options a module is compiled with depend on which target fetches it first.
//! Clean does not model that race: it computes the arguments of every route
//! that can reach the module and uses them when they agree, and refuses the
//! module when they differ. That refusal can be stricter than one particular
//! `lake build` invocation; it never compiles a module under options Lake's
//! build of the same target would not use.

use crate::config::{LakeConfig, LeanExe, LeanLib, LeanOption, PackageConfig};
use crate::error::{LakeError, LakeResult};
use crate::glob::{GlobKind, ModuleGlob};
use crate::workspace::Workspace;
use clean_kernel::Name;

impl Workspace {
    /// The arguments Lake passes `lean` when it compiles `module`, in Lake's
    /// order: the `weakLeanArgs`, then `-D<name>=<value>` for each
    /// `leanOptions` entry and the `moreLeanArgs` entries verbatim, package
    /// before target. `-D` is last-wins, so the order is what decides a name
    /// set at several levels.
    ///
    /// # Errors
    ///
    /// [`LakeError::InvalidConfig`] when the owning package's lakefile cannot
    /// be read, when the package or a target that can compile `module` has an
    /// option value the lakefile parser could not read, or when the targets
    /// that can compile `module` give it different arguments: in each case
    /// the options Lake would compile `module` with are not known, and
    /// building it under different ones could accept what Lake's build
    /// refuses.
    pub fn module_lean_args(&self, module: &str) -> LakeResult<Vec<String>> {
        let name = Self::parse_module_name(module)?;
        match self.module_package_dir(&name) {
            None => lean_args_in(self.config(), module, &name),
            Some(dir) => {
                let config = LakeConfig::load_from_dir(&dir).map_err(|e| {
                    LakeError::InvalidConfig(format!(
                        "cannot build {module}: its package at {} has a lakefile Clean cannot \
                         read ({e}), so the options Lake compiles it with are unknown",
                        dir.display()
                    ))
                })?;
                lean_args_in(&config, module, &name)
            }
        }
    }
}

/// [`Workspace::module_lean_args`] within the package `config` owns.
fn lean_args_in(config: &LakeConfig, module: &str, name: &Name) -> LakeResult<Vec<String>> {
    let package = &config.package;
    refuse_unreadable(
        module,
        "package",
        &package.name,
        &package.unreadable_lean_args,
    )?;
    let mut routes: Vec<(String, Vec<String>)> = Vec::new();
    // `Package.findModule?`: the last library that can build it.
    let mut found = None;
    for lib in config.libs.iter().rev() {
        if lib_can_build(lib, name)? {
            found = Some(lib);
            break;
        }
    }
    // A library target builds its own roots through itself.
    let rooted = config.libs.iter().filter(|lib| {
        lib.root_modules()
            .iter()
            .any(|root| Workspace::parse_module_name(root).is_ok_and(|r| r == *name))
    });
    let mut seen: Vec<&str> = Vec::new();
    for lib in found.into_iter().chain(rooted) {
        if seen.contains(&lib.name.as_str()) {
            continue;
        }
        seen.push(&lib.name);
        refuse_unreadable(module, "lean_lib", &lib.name, &lib.unreadable_lean_args)?;
        routes.push((
            format!("lean_lib `{}`", lib.name),
            target_args(
                package,
                &lib.weak_lean_args,
                &lib.lean_options,
                &lib.more_lean_args,
            ),
        ));
    }
    // `LeanExe.root`: the executable's root through `toLeanLib`.
    for exe in config.exes.iter().filter(|exe| exe_root_is(exe, name)) {
        refuse_unreadable(module, "lean_exe", &exe.name, &exe.unreadable_lean_args)?;
        routes.push((
            format!("lean_exe `{}`", exe.name),
            target_args(
                package,
                &exe.weak_lean_args,
                &exe.lean_options,
                &exe.more_lean_args,
            ),
        ));
    }
    let Some((_, first)) = routes.first() else {
        // No target can compile it: the package's arguments alone.
        return Ok(target_args(package, &[], &[], &[]));
    };
    if let Some((other, args)) = routes.iter().find(|(_, args)| args != first) {
        let (route, _) = &routes[0];
        return Err(LakeError::InvalidConfig(format!(
            "cannot build {module}: Lake compiles it with different arguments depending on the \
             target that reaches it ({route}: [{}]; {other}: [{}]), so which options apply is \
             decided by build order; Clean refuses rather than pick one",
            first.join(" "),
            args.join(" ")
        )));
    }
    Ok(first.clone())
}

/// Lake's `weakLeanArgs ++ leanArgs` for one target of `package`.
fn target_args(
    package: &PackageConfig,
    weak: &[String],
    options: &[LeanOption],
    more: &[String],
) -> Vec<String> {
    let defines = |options: &[LeanOption]| {
        options
            .iter()
            .map(|o| format!("-D{}", o.define_arg()))
            .collect::<Vec<_>>()
    };
    let mut args = package.weak_lean_args.clone();
    args.extend_from_slice(weak);
    args.extend(defines(&package.lean_options));
    args.extend_from_slice(&package.more_lean_args);
    args.extend(defines(options));
    args.extend_from_slice(more);
    args
}

/// Lake's `LeanLibConfig.isBuildableModule`: a glob matches the module, or a
/// root is a component prefix of it AND a glob matches that root. A library
/// with no `globs` has Lake's default, one `.one` glob per root.
fn lib_can_build(lib: &LeanLib, name: &Name) -> LakeResult<bool> {
    let roots = lib
        .root_modules()
        .iter()
        .map(|root| Workspace::parse_module_name(root))
        .collect::<LakeResult<Vec<Name>>>()?;
    let globs: Vec<(Name, GlobKind)> = if lib.globs.is_empty() {
        roots
            .iter()
            .map(|root| (root.clone(), GlobKind::One))
            .collect()
    } else {
        lib.globs
            .iter()
            .map(|spec| -> LakeResult<(Name, GlobKind)> {
                let glob = ModuleGlob::parse(spec).ok_or_else(|| {
                    LakeError::InvalidConfig(format!("invalid module glob: {spec}"))
                })?;
                Ok((Workspace::parse_module_name(&glob.module)?, glob.kind))
            })
            .collect::<LakeResult<_>>()?
    };
    let matches = |candidate: &Name| {
        globs.iter().any(|(base, kind)| match kind {
            GlobKind::One => candidate == base,
            GlobKind::AndSubmodules => Workspace::name_is_under(candidate, base),
            GlobKind::Submodules => candidate != base && Workspace::name_is_under(candidate, base),
        })
    };
    Ok(matches(name)
        || roots
            .iter()
            .any(|root| Workspace::name_is_under(name, root) && matches(root)))
}

fn exe_root_is(exe: &LeanExe, name: &Name) -> bool {
    Workspace::parse_module_name(&exe.root).is_ok_and(|root| root == *name)
}

fn refuse_unreadable(module: &str, kind: &str, target: &str, lines: &[String]) -> LakeResult<()> {
    match lines.first() {
        None => Ok(()),
        Some(line) => Err(LakeError::InvalidConfig(format!(
            "cannot build {module}: {kind} `{target}` sets `{line}`, which Clean's lakefile \
             reader cannot evaluate or cannot attribute to a target, so the options Lake \
             compiles this module with are unknown (Clean reads array literals of `⟨`name, \
             value⟩` in a target's `where` block; refusing rather than building under \
             different options)"
        ))),
    }
}

#[cfg(test)]
#[path = "module_options_tests.rs"]
mod tests;
