// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::manifest::{GitPackage, LakeManifestVersion};

#[test]
fn test_parse_minimal_lakefile() {
    let content = r"
import Lake
open Lake DSL

package test
lean_lib Test
";
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.package.name, "test");
    assert_eq!(config.libs.len(), 1);
    assert_eq!(config.libs[0].name, "Test");
}

#[test]
fn test_parse_lakefile_with_where() {
    let content = r#"
import Lake
open Lake DSL

package myproject where
  version := "0.1.0"

@[default_target]
lean_lib MyLib where
  roots := #[`MyLib]

lean_exe myexe where
  root := `Main
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.package.name, "myproject");
    assert_eq!(config.package.version, Some("0.1.0".to_string()));
    assert_eq!(config.libs.len(), 1);
    assert_eq!(config.libs[0].name, "MyLib");
    assert_eq!(config.libs[0].roots, vec!["MyLib"]);
    assert_eq!(config.exes.len(), 1);
    assert_eq!(config.exes[0].name, "myexe");
    assert_eq!(config.exes[0].root, "Main");
    assert_eq!(config.default_targets, vec!["MyLib"]);
}

#[test]
fn test_parse_name_array() {
    assert_eq!(
        LakeConfig::parse_name_array("#[`A, `B, `C]"),
        vec!["A", "B", "C"]
    );
    assert_eq!(LakeConfig::parse_name_array("`Single"), vec!["Single"]);
}

#[test]
fn test_package_config_minimal() {
    let pkg = PackageConfig::minimal("test");
    assert_eq!(pkg.name, "test");
    assert!(
        pkg.version.is_none(),
        "minimal package should have no version"
    );
}

#[test]
fn test_parse_more_lean_args() {
    let content = r#"
import Lake
open Lake DSL

package test where
  moreLeanArgs := #["-DautoImplicit=false", "-Dpp.all"]
  moreLinkArgs := #["-L/usr/local/lib", "-lmylib"]

lean_lib Test
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.package.name, "test");
    assert_eq!(
        config.package.more_lean_args,
        vec!["-DautoImplicit=false", "-Dpp.all"]
    );
    assert_eq!(
        config.package.more_link_args,
        vec!["-L/usr/local/lib", "-lmylib"]
    );
}

#[test]
fn test_lean_lib_root_modules() {
    let lib = LeanLib::minimal("MyLib");
    assert_eq!(lib.root_modules(), vec!["MyLib"]);

    let lib_with_roots = LeanLib {
        name: "MyLib".to_string(),
        roots: vec!["MyLib.Core".to_string(), "MyLib.Utils".to_string()],
        ..Default::default()
    };
    assert_eq!(
        lib_with_roots.root_modules(),
        vec!["MyLib.Core", "MyLib.Utils"]
    );
}

#[test]
fn test_parse_require_git_dependency() {
    let content = r#"
import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "1.2.3"

package demo
lean_lib Demo
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.package.dependencies.len(), 1);
    let dep = &config.package.dependencies[0];
    assert_eq!(dep.name, "std");
    assert_eq!(
        dep.git.as_deref(),
        Some("https://github.com/leanprover/std4")
    );
    assert_eq!(dep.version.as_deref(), Some("1.2.3"));
}

#[test]
fn test_validate_manifest_semver_constraint() {
    let dep = Dependency {
        name: "std".to_string(),
        git: Some("https://github.com/leanprover/std4".to_string()),
        rev: None,
        path: None,
        version: Some("^1.2".to_string()),
        scope: None,
        sub_dir: None,
    };

    let manifest = LakeManifest {
        version: LakeManifestVersion::Numeric(7),
        packages_dir: ".lake/packages".to_string(),
        packages: vec![ManifestPackage::Git(GitPackage {
            name: "std".to_string(),
            url: "https://github.com/leanprover/std4".to_string(),
            rev: "1.2.5".to_string(),
            input_rev: None,
            ..Default::default()
        })],
    };

    PackageConfig {
        name: "demo".to_string(),
        dependencies: vec![dep],
        ..Default::default()
    }
    .validate_manifest(&manifest)
    .unwrap();
}

#[test]
fn test_validate_manifest_mismatch() {
    let dep = Dependency {
        name: "std".to_string(),
        git: Some("https://github.com/leanprover/std4".to_string()),
        rev: Some("main".to_string()),
        path: None,
        version: None,
        scope: None,
        sub_dir: None,
    };

    let manifest = LakeManifest {
        version: LakeManifestVersion::Numeric(7),
        packages_dir: ".lake/packages".to_string(),
        packages: vec![ManifestPackage::Git(GitPackage {
            name: "std".to_string(),
            url: "https://github.com/leanprover/std4".to_string(),
            rev: "dev-branch".to_string(),
            input_rev: None,
            ..Default::default()
        })],
    };

    let result = PackageConfig {
        name: "demo".to_string(),
        dependencies: vec![dep],
        ..Default::default()
    }
    .validate_manifest(&manifest);

    assert!(
        matches!(result, Err(LakeError::DependencyMismatch { .. })),
        "expected DependencyMismatch, got: {result:?}"
    );
}

#[test]
fn test_parse_lakefile_with_tests() {
    let content = r"
import Lake
open Lake DSL

package myproject

lean_lib MyLib

lean_test mytest where
  root := `Test.Main

lean_test integration where
  root := `Test.Integration
";
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.package.name, "myproject");
    assert_eq!(config.libs.len(), 1);
    assert_eq!(config.tests.len(), 2);
    assert_eq!(config.tests[0].name, "mytest");
    assert_eq!(config.tests[0].root, "Test.Main");
    assert_eq!(config.tests[1].name, "integration");
    assert_eq!(config.tests[1].root, "Test.Integration");
}

#[test]
fn test_lean_test_minimal() {
    let test = LeanTest::minimal("unit", "Test.Unit");
    assert_eq!(test.name, "unit");
    assert_eq!(test.root, "Test.Unit");
}

#[test]
fn test_parse_lakefile_with_scripts() {
    let content = r#"
import Lake
open Lake DSL

package myproject

lean_lib MyLib

script hello where
  doc := "Prints hello"
  IO.println "Hello, World!"

script build_docs :=
  do
    IO.println "Building docs..."
    pure 0
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.package.name, "myproject");
    assert_eq!(config.scripts.len(), 2);
    assert_eq!(config.scripts[0].name, "hello");
    assert_eq!(config.scripts[0].doc, Some("Prints hello".to_string()));
    assert!(config.scripts[0].body.contains("IO.println"));
    assert_eq!(config.scripts[1].name, "build_docs");
    assert!(config.scripts[1].body.contains("Building docs"));
}

#[test]
fn test_lake_script_default() {
    let script = LakeScript::default();
    assert!(script.name.is_empty());
    assert!(script.body.is_empty());
    assert!(
        script.doc.is_none(),
        "default LakeScript should have no doc"
    );
    assert!(
        script.args.is_none(),
        "default LakeScript should declare no argument binder"
    );
}

/// Lean's `script <name> do` form: the name is the NAME, and the body is
/// kept.
///
/// Measured 2026-08-27 against the shipped binary before this fix:
/// `clean lake script list` printed `hello do` and `clean lake script doc
/// "hello do"` printed an empty body — the whole header remainder became
/// the name and every indented body line was dropped without a
/// diagnostic (body lines are indented, so they are not recorded as
/// skipped top-level constructs either).
#[test]
fn test_parse_script_do_form_keeps_name_and_body() {
    let content =
        "package demo\n\nscript hello do\n  IO.println \"hello\"\n  IO.println \"again\"\n";
    let config = LakeConfig::parse(content).expect("do-form script should parse");

    assert_eq!(config.scripts.len(), 1);
    assert_eq!(config.scripts[0].name, "hello", "name must not carry ` do`");
    assert_eq!(
        config.scripts[0].body, "do\nIO.println \"hello\"\nIO.println \"again\"",
        "the `do` opens the body and both statements must survive"
    );
    assert!(config.scripts[0].args.is_none());
}

/// `script <name> (args) do`: the binder is recorded, not folded into the
/// name.
#[test]
fn test_parse_script_do_form_with_binder_records_binder_separately() {
    let content = "package demo\n\nscript greet (args) do\n  IO.println \"hi\"\n";
    let config = LakeConfig::parse(content).expect("binder do-form should parse");

    assert_eq!(config.scripts.len(), 1);
    assert_eq!(config.scripts[0].name, "greet");
    assert_eq!(config.scripts[0].args.as_deref(), Some("args"));
    assert!(config.scripts[0].body.contains("IO.println \"hi\""));
}

/// A name that merely ENDS in the letters `do` is not a `do` form.
#[test]
fn test_parse_script_name_ending_in_do_is_not_split() {
    let config =
        LakeConfig::parse("package demo\n\nscript tornado\n").expect("bare script should parse");
    assert_eq!(config.scripts.len(), 1);
    assert_eq!(config.scripts[0].name, "tornado");
    assert!(config.scripts[0].body.is_empty());
}

/// `script <name> := do` puts the `do` on the header line; dropping it
/// would leave a bare statement sequence that no longer sequences.
#[test]
fn test_parse_script_inline_assign_head_opens_the_body() {
    let content = "package demo\n\nscript build := do\n  IO.println \"building\"\n";
    let config = LakeConfig::parse(content).expect("`:= do` script should parse");

    assert_eq!(config.scripts.len(), 1);
    assert_eq!(config.scripts[0].name, "build");
    assert_eq!(
        config.scripts[0].body, "do\nIO.println \"building\"",
        "the header-line `do` must head the body"
    );
}

/// A single-expression `script <name> := <term>` keeps the term.
#[test]
fn test_parse_script_inline_assign_term_is_the_body() {
    let config = LakeConfig::parse("package demo\n\nscript p := IO.println \"x\"\n")
        .expect("inline-term script should parse");
    assert_eq!(config.scripts[0].name, "p");
    assert_eq!(config.scripts[0].body, "IO.println \"x\"");
}

/// A script block ends at column 0: a following declaration must not be
/// swallowed into the body (and must still be accounted as skipped).
#[test]
fn test_parse_script_block_stops_at_column_zero() {
    let content =
            "package demo\n\nscript hello do\n  IO.println \"hi\"\n\ndef leftover := 1\n\nlean_lib MyLib\n";
    let config = LakeConfig::parse(content).expect("parse");

    assert_eq!(config.scripts.len(), 1);
    assert_eq!(config.scripts[0].body, "do\nIO.println \"hi\"");
    assert_eq!(
        config.libs.len(),
        1,
        "the lean_lib after the script is kept"
    );
    assert!(
        config
            .diagnostics
            .iter()
            .any(|d| d.token == "def" && d.text.contains("leftover")),
        "the dedented `def` is a skipped top-level construct, not script body: {:?}",
        config.diagnostics
    );
}

#[test]
fn test_split_script_header_forms() {
    let do_form = LakeConfig::split_script_header("hello do");
    assert_eq!(do_form.name, "hello");
    assert_eq!(do_form.args, None);
    assert_eq!(do_form.inline_body, Some("do"));
    assert!(do_form.has_block);

    let binder = LakeConfig::split_script_header("greet (args) do");
    assert_eq!(binder.name, "greet");
    assert_eq!(binder.args, Some("args"));

    let where_form = LakeConfig::split_script_header("hello where");
    assert_eq!(where_form.name, "hello");
    assert_eq!(where_form.inline_body, None);
    assert!(where_form.has_block);

    let bare = LakeConfig::split_script_header("hello");
    assert_eq!(bare.name, "hello");
    assert!(!bare.has_block);
}

#[test]
fn test_parse_mathlib_style_lakefile() {
    // Test parsing a Mathlib-style lakefile with modern require syntax
    let content = r#"
import Lake

open Lake DSL

/-!
## Dependencies
-/

require "leanprover-community" / "batteries" @ git "main"
require "leanprover-community" / "Qq" @ git "master"
require "leanprover-community" / "aesop" @ git "master"

package mathlib where
  testDriver := "MathlibTest"

/-!
## Libraries
-/

@[default_target]
lean_lib Mathlib where
  leanOptions := mathlibLeanOptions

lean_lib Cache
lean_lib LongestPole

lean_lib MathlibTest where
  globs := #[.submodules `MathlibTest]

/-- Documentation library -/
lean_lib docs where
  roots := #[`docs]

/-!
## Executables
-/

/-- Adds labels to PRs -/
lean_exe autolabel where
  srcDir := "scripts"

lean_exe cache where
  root := `Cache.Main

lean_exe «check-yaml» where
  srcDir := "scripts"
  supportInterpreter := true

lean_exe mk_all where
  srcDir := "scripts"
  supportInterpreter := true
  weakLinkArgs := #["-lLake"]
"#;
    let config = LakeConfig::parse(content).unwrap();

    // Check package
    assert_eq!(config.package.name, "mathlib");

    // Check dependencies - should parse "owner" / "repo" format
    assert!(
        config.package.dependencies.len() >= 3,
        "Expected at least 3 dependencies, got {}",
        config.package.dependencies.len()
    );

    // Check libraries
    assert!(
        config.libs.len() >= 5,
        "Expected at least 5 libraries, got {}",
        config.libs.len()
    );
    let lib_names: Vec<_> = config.libs.iter().map(|l| l.name.as_str()).collect();
    assert!(lib_names.contains(&"Mathlib"));
    assert!(lib_names.contains(&"Cache"));
    assert!(lib_names.contains(&"docs"));

    // Check executables - should handle guillemet names
    assert!(
        config.exes.len() >= 4,
        "Expected at least 4 executables, got {}",
        config.exes.len()
    );
    let exe_names: Vec<_> = config.exes.iter().map(|e| e.name.as_str()).collect();
    assert!(exe_names.contains(&"autolabel"));
    assert!(exe_names.contains(&"cache"));
    assert!(exe_names.contains(&"mk_all"));

    // Check default target
    assert!(config.default_targets.contains(&"Mathlib".to_string()));

    // Every TOP-LEVEL construct in this fixture is modeled. The fields
    // inside `where` blocks are not, and this assertion is the point of the
    // fixture: a real Mathlib lakefile carries `testDriver`, `leanOptions`,
    // `supportInterpreter` and `weakLinkArgs`, none of which the
    // declarative subset models. They used to be dropped in silence, so the
    // config looked fully understood while `lake test` reported "No test
    // targets defined in lakefile.lean". They are now accounted for.
    let skipped: Vec<&str> = config
        .diagnostics
        .iter()
        .map(|d| d.token.as_str())
        .collect();
    assert_eq!(
        skipped,
        vec![
            "testDriver",
            "leanOptions",
            "supportInterpreter",
            "supportInterpreter",
            "weakLinkArgs",
        ],
        "unmodelled `where`-block fields must be accounted for, not dropped: {:?}",
        config.diagnostics
    );
    // Doc comments and section headers inside a `where` block are comments,
    // not fields, and must not be reported as skipped.
    assert!(
        !config
            .diagnostics
            .iter()
            .any(|d| d.token.starts_with("/-") || d.token.starts_with("##")),
        "comments inside a `where` block must not be reported: {:?}",
        config.diagnostics
    );
}

#[test]
fn test_parse_records_skipped_top_level_constructs() {
    let content = r"import Lake
open Lake DSL

package demo

abbrev extraOptions := #[]

lean_lib Demo
";
    let config = LakeConfig::parse(content).expect("lenient parse should succeed");
    assert_eq!(config.package.name, "demo");
    assert_eq!(config.libs.len(), 1);
    assert_eq!(
        config.diagnostics.len(),
        1,
        "exactly the abbrev should be skipped: {:?}",
        config.diagnostics
    );
    assert_eq!(config.diagnostics[0].line, 6);
    assert_eq!(config.diagnostics[0].token, "abbrev");
    assert_eq!(config.diagnostics[0].text, "abbrev extraOptions := #[]");
}

#[test]
fn test_parse_records_unmodelled_where_block_fields() {
    let content = r#"import Lake
open Lake DSL

package demo where
  testDriver := "DemoTest"
  moreLeanArgs := #["-DwarningAsError=true"]

lean_lib Demo where
  roots := #[`Demo]
  precompileModules := true
"#;
    let config = LakeConfig::parse(content).expect("lenient parse should succeed");
    // The modelled field is still parsed.
    assert_eq!(config.package.more_lean_args, vec!["-DwarningAsError=true"]);
    assert_eq!(config.libs[0].roots, vec!["Demo"]);
    // The two unmodelled ones are accounted for rather than dropped.
    let skipped: Vec<(usize, &str)> = config
        .diagnostics
        .iter()
        .map(|d| (d.line, d.token.as_str()))
        .collect();
    assert_eq!(skipped, vec![(5, "testDriver"), (10, "precompileModules")]);
}

#[test]
fn test_parse_strict_mode_errors_on_unmodelled_where_block_field() {
    // A dropped `testDriver` is why a TOML/lean project with a test driver
    // reported "No test targets defined"; strict mode must refuse it rather
    // than under-parse, exactly as it refuses an unmodelled top-level
    // construct.
    let content = r#"import Lake
open Lake DSL

package demo where
  testDriver := "DemoTest"

lean_lib Demo
"#;
    match LakeConfig::parse_with_mode(content, LakefileParseMode::Strict) {
        Err(LakeError::UnrecognizedConstructs { count, summary }) => {
            assert_eq!(count, 1, "only testDriver is unmodelled");
            assert!(
                summary.contains("testDriver"),
                "summary should name the field: {summary}"
            );
        }
        other => panic!("strict mode must reject an unmodelled field, got {other:?}"),
    }
}

#[test]
fn test_parse_strict_mode_errors_on_unrecognized_construct() {
    let content = r"import Lake
open Lake DSL

package demo

target customStep pkg : Unit := do
  pure ()

lean_lib Demo
";
    let result = LakeConfig::parse_with_mode(content, LakefileParseMode::Strict);
    match result {
        Err(LakeError::UnrecognizedConstructs { count, summary }) => {
            assert_eq!(count, 1, "only the target declaration is unrecognized");
            assert!(
                summary.contains("line 6: `target`"),
                "summary should name the construct and line: {summary}"
            );
        }
        other => panic!("expected UnrecognizedConstructs, got: {other:?}"),
    }
}

#[test]
fn test_parse_strict_mode_accepts_fully_modeled_lakefile() {
    let content = r"
import Lake
open Lake DSL

package test
lean_lib Test
";
    let config = LakeConfig::parse_with_mode(content, LakefileParseMode::Strict)
        .expect("strict parse of a fully-modeled lakefile should succeed");
    assert!(config.diagnostics.is_empty(), "no skipped constructs");
}

#[test]
fn test_parse_block_comments_produce_no_diagnostics() {
    let content = r"import Lake
open Lake DSL

/-!
## Module docs spanning
several lines
-/

/-- Single-line doc comment -/
package demo

lean_lib Demo
";
    let config = LakeConfig::parse_with_mode(content, LakefileParseMode::Strict)
        .expect("block comments must not count as skipped constructs");
    assert_eq!(config.package.name, "demo");
    assert!(config.diagnostics.is_empty());
}

#[test]
fn test_parse_indented_continuation_lines_not_double_counted() {
    // A multi-line skipped construct is accounted once (its head line);
    // indented continuations and a dangling closing bracket carry no
    // entries of their own.
    let content = r"import Lake
open Lake DSL

package demo

abbrev linters : Array LeanOption := #[
  first,
  second
]

lean_lib Demo
";
    let config = LakeConfig::parse(content).expect("lenient parse should succeed");
    let heads: Vec<(usize, &str)> = config
        .diagnostics
        .iter()
        .map(|skipped| (skipped.line, skipped.token.as_str()))
        .collect();
    assert_eq!(
        heads,
        vec![(6, "abbrev")],
        "only the construct head line is recorded"
    );
}

#[test]
fn test_lakefile_parse_mode_from_env() {
    crate::test_env::with_serialized_env_vars(&[(LakefileParseMode::STRICT_ENV, "1")], || {
        assert_eq!(LakefileParseMode::from_env(), LakefileParseMode::Strict)
    });
    crate::test_env::with_serialized_env_vars(&[(LakefileParseMode::STRICT_ENV, "0")], || {
        assert_eq!(LakefileParseMode::from_env(), LakefileParseMode::Lenient)
    });
    crate::test_env::with_serialized_env_vars(&[(LakefileParseMode::STRICT_ENV, "")], || {
        assert_eq!(LakefileParseMode::from_env(), LakefileParseMode::Lenient)
    });
}

#[test]
fn test_parse_require_new_syntax() {
    // Test the new "owner" / "repo" @ git "branch" syntax
    let content = r#"
import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "main"
require "leanprover-community" / "Qq" @ git "v1.0.0"

package test
lean_lib Test
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.package.dependencies.len(), 2);

    let batteries = &config.package.dependencies[0];
    assert_eq!(batteries.name, "batteries");
    assert!(batteries.git.is_some(), "batteries dep should have git url");
    assert_eq!(batteries.rev.as_deref(), Some("main"));

    let qq = &config.package.dependencies[1];
    assert_eq!(qq.name, "Qq");
    assert!(qq.git.is_some(), "Qq dep should have git url");
}

#[test]
fn test_parse_interpolates_package_name_builtin() {
    // A value referencing the built-in PACKAGE_NAME variable resolves.
    let content = r#"
import Lake
open Lake DSL

package demo where
  description := "library for $(PACKAGE_NAME)"

lean_lib Demo
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.package.name, "demo");
    assert_eq!(
        config.package.description.as_deref(),
        Some("library for demo")
    );
}

#[test]
fn test_parse_interpolates_env_variable() {
    // A value referencing an environment variable resolves via fallback.
    let key = "CLEAN_LAKE_CONFIG_INTERP_TEST";
    let content = format!(
        r#"
import Lake
open Lake DSL

package demo where
  srcDir := "${{{key}}}/src"

lean_lib Demo
"#
    );
    let config = crate::test_env::with_serialized_env_vars(&[(key, "envroot")], || {
        LakeConfig::parse(&content)
    })
    .unwrap();
    assert_eq!(config.package.src_dir, Some(PathBuf::from("envroot/src")));
}

#[test]
fn test_parse_interpolation_unknown_variable_errors() {
    let content = r#"
import Lake
open Lake DSL

package demo where
  description := "needs $(DEFINITELY_NOT_SET_VARIABLE_XYZ)"

lean_lib Demo
"#;
    let result = LakeConfig::parse(content);
    assert!(
        matches!(
            result,
            Err(LakeError::UnknownVariable { ref name, .. })
                if name == "DEFINITELY_NOT_SET_VARIABLE_XYZ"
        ),
        "expected UnknownVariable, got: {result:?}"
    );
}

#[test]
fn test_parse_interpolation_in_more_lean_args() {
    let content = r#"
import Lake
open Lake DSL

package demo where
  moreLeanArgs := #["-Dname=$(PACKAGE_NAME)", "-Dplain"]

lean_lib Demo
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(
        config.package.more_lean_args,
        vec!["-Dname=demo", "-Dplain"]
    );
}

#[test]
fn test_parse_no_interpolation_leaves_value_unchanged() {
    // A literal value with no references must pass through untouched,
    // including a lone dollar sign.
    let content = r#"
import Lake
open Lake DSL

package demo where
  description := "cost is $5 flat"

lean_lib Demo
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(
        config.package.description.as_deref(),
        Some("cost is $5 flat")
    );
}

#[test]
fn test_parse_guillemet_name() {
    // Test parsing names with guillemets (French quotes) «name»
    let content = r"
import Lake
open Lake DSL

package test

lean_exe «check-yaml» where
  root := `CheckYaml
";
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.exes.len(), 1);
    assert_eq!(config.exes[0].name, "check-yaml");
}

#[test]
fn test_parse_lib_default_facets_and_pre_compile_hooks_populated() {
    let content = r#"
import Lake
open Lake DSL

package test

lean_lib MyLib where
  roots := #[`MyLib]
  defaultFacets := #["leanArts", "static"]
  preCompileHooks := #["gen-headers", "codegen"]

lean_exe runner where
  root := `Main
  supportedBackends := #["native", "llvm"]
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.libs.len(), 1);
    assert_eq!(
        config.libs[0].default_facets,
        vec!["leanArts", "static"],
        "defaultFacets must be parsed into the lib struct"
    );
    assert_eq!(
        config.libs[0].pre_compile_hooks,
        vec!["gen-headers", "codegen"],
        "preCompileHooks must be parsed into the lib struct"
    );
    assert_eq!(config.exes.len(), 1);
    assert_eq!(
        config.exes[0].supported_backends,
        vec!["native", "llvm"],
        "supportedBackends must be parsed into the exe struct"
    );
}

#[test]
fn test_parse_lib_exe_without_extra_fields_defaults_empty() {
    // Regression: a lakefile that does not declare the new fields must keep
    // them at their empty defaults rather than gaining spurious entries.
    let content = r#"
import Lake
open Lake DSL

package test

lean_lib MyLib where
  roots := #[`MyLib]

lean_exe runner where
  root := `Main
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.libs.len(), 1);
    assert!(
        config.libs[0].default_facets.is_empty(),
        "default_facets should default empty when undeclared"
    );
    assert!(
        config.libs[0].pre_compile_hooks.is_empty(),
        "pre_compile_hooks should default empty when undeclared"
    );
    assert_eq!(config.exes.len(), 1);
    assert!(
        config.exes[0].supported_backends.is_empty(),
        "supported_backends should default empty when undeclared"
    );
}

#[test]
fn test_parse_interpolation_in_lib_default_facets() {
    // The interpolate loop must cover the newly-parsed fields so that
    // declared $(VAR) references are honored rather than left raw.
    let content = r#"
import Lake
open Lake DSL

package demo

lean_lib MyLib where
  defaultFacets := #["$(PACKAGE_NAME)-arts"]

lean_exe runner where
  root := `Main
  supportedBackends := #["$(PACKAGE_NAME)-backend"]
"#;
    let config = LakeConfig::parse(content).unwrap();
    assert_eq!(config.libs[0].default_facets, vec!["demo-arts"]);
    assert_eq!(config.exes[0].supported_backends, vec!["demo-backend"]);
}
