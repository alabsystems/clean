// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module trust over what an artifact carries BESIDE its declarations:
//! structure field tables, one record per name, Lean-built parts, visibility
//! marks, and class and instance entries.

use super::*;

// ── elaborator metadata: the structure field table (round 27) ─────────────────

const STRUCT_LIB: &str = "structure K1Lib.P where
  x : Nat
  y : Nat
";

/// `(K1Lib.P.mk 0 1).x = 1` is FALSE in the library's source (Lean 4.8.0
/// rejects it); `= 0` is true.
const STRUCT_USE_FALSE: &str = "import K1Lib

theorem K1Use.px : (K1Lib.P.mk 0 1).x = 1 := rfl
";
const STRUCT_USE_TRUE: &str = "import K1Lib

theorem K1Use.px : (K1Lib.P.mk 0 1).x = 0 := rfl
";

fn struct_table_is(env: &Environment, fields: &[&str]) -> bool {
    env.get_structure_field_names(&name("K1Lib.P"))
        .is_some_and(|t| {
            t.iter()
                .map(ToString::to_string)
                .eq(fields.iter().map(|f| (*f).to_string()))
        })
}

/// Build STRUCT_LIB with a dependent citing `use_source`; tamper the
/// library's payload with `edit`, re-stamp its trace (so the build REUSES the
/// tampered artifact), rebuild.
fn struct_project_after_tamper(
    root: &Path,
    tag: &str,
    use_source: &str,
    edit: impl FnOnce(&mut CleanPayload),
) -> BuildResult {
    let dir = root.join(tag);
    write_project(
        &dir,
        &["K1Lib", "K1Use"],
        &[("K1Lib", STRUCT_LIB), ("K1Use", STRUCT_USE_TRUE)],
    );
    let first = build(&dir);
    assert!(
        first.failed.is_empty(),
        "{tag}: genuine project must build: {first:?}"
    );
    tamper(&dir, "K1Lib", edit);
    restamp_trace(&dir, "K1Lib");
    fs::write(dir.join("K1Use.lean"), use_source).expect("rewrite dependent");
    build(&dir)
}

fn reverse_table(p: &mut CleanPayload) {
    let (_, fields) = p
        .structure_fields
        .iter_mut()
        .find(|(s, _)| s == &name("K1Lib.P"))
        .expect("the payload carries K1Lib.P's field table");
    fields.reverse();
}

/// M9 of the round-27 verification: `P.x`'s value replaced by `P.y`'s
/// (well-typed), table left honest.
fn swap_projection_x(p: &mut CleanPayload) {
    let y = constant_mut(p, &name("K1Lib.P.y")).value.clone();
    constant_mut(p, &name("K1Lib.P.x")).value = y;
}

#[test]
fn a_genuine_structure_artifact_loads_with_its_table_and_elaborates_honestly() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", STRUCT_LIB);
    let (env, _) = load(&dir, "K1Lib");
    assert!(
        struct_table_is(&env, &["x", "y"]),
        "genuine table [x, y] must load"
    );

    // The false statement is refused and the true one builds over the genuine
    // artifact, so a refusal below cannot come from a fixture that never
    // worked.
    let proj = tmp.path().join("proj");
    write_project(
        &proj,
        &["K1Lib", "K1Use"],
        &[("K1Lib", STRUCT_LIB), ("K1Use", STRUCT_USE_FALSE)],
    );
    let result = build(&proj);
    assert!(
        result.failed.iter().any(|(m, _)| m == "K1Use"),
        "control: `(P.mk 0 1).x = 1` must not build over the genuine artifact: {result:?}"
    );
    let result = struct_project_after_tamper(tmp.path(), "proj2", STRUCT_USE_TRUE, |_| {});
    assert!(
        result.failed.is_empty(),
        "control: the true statement builds: {result:?}"
    );
}

#[test]
fn a_reversed_structure_field_table_is_refused_at_import() {
    // Measured on d0789d05f (M8f): the reversed table made
    // `(V0.P.mk 0 1).x = 1 := rfl` pass `clean check`, `clean export-cert`
    // and a dependent's `clean lake build`.
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", STRUCT_LIB);
    tamper(&dir, "K1Lib", reverse_table);
    let mut env = builder_base().0;
    let err = clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(&dir))
        .expect_err("a table contradicting the artifact's own projections must refuse the import");
    assert!(
        matches!(
            err,
            clean_olean::ImportError::InconsistentStructureTable { .. }
        ),
        "{err}"
    );

    let result = struct_project_after_tamper(tmp.path(), "proj", STRUCT_USE_FALSE, reverse_table);
    let failure = result
        .failed
        .iter()
        .find(|(m, _)| m == "K1Use")
        .unwrap_or_else(|| panic!("K1Use.px : (P.mk 0 1).x = 1 must not build: {result:?}"));
    assert!(failure.1.contains("inconsistent artifact"), "{failure:?}");
}

#[test]
fn a_projection_rewritten_under_an_honest_table_is_refused_at_import() {
    // The table and the projection disagree the other way round. Dropping
    // the table instead of refusing (a first draft of the round-27 fix) let
    // `.x` resolve to the rewritten projection, and `(V0.P.mk 0 1).x = 1`
    // passed where the unfixed tree refused it.
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", STRUCT_LIB);
    tamper(&dir, "K1Lib", swap_projection_x);
    let mut env = builder_base().0;
    let err = clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(&dir))
        .expect_err("a projection contradicting the table must refuse the import");
    assert!(
        matches!(
            err,
            clean_olean::ImportError::InconsistentStructureTable { .. }
        ),
        "{err}"
    );

    let result =
        struct_project_after_tamper(tmp.path(), "proj", STRUCT_USE_FALSE, swap_projection_x);
    assert!(
        result.failed.iter().any(|(m, _)| m == "K1Use"),
        "K1Use.px : (P.mk 0 1).x = 1 must not build: {result:?}"
    );
}

// ── round 28: the table is what the projections compute; one name, one record ─

/// Y1 of the round-28 verification: the table reversed AND both projections
/// rewritten to equivalent recursor bodies,
/// `P.x := fun s => P.rec (motive := fun _ => Nat) (fun a b => a) s` — the
/// honest meaning, but not `λ*. Proj(P, i, _)`-shaped. Measured on
/// `e3f696689`: `(V0.P.mk 0 1).x = 1` passed check, export-cert and a
/// forged-trace build with a dependent.
fn reverse_table_over_recursor_projections(p: &mut CleanPayload) {
    reverse_table(p);
    let p_ty = Expr::const_(name("K1Lib.P"), vec![]);
    let nat = Expr::const_(name("Nat"), vec![]);
    for (field, pick) in [("K1Lib.P.x", 1u32), ("K1Lib.P.y", 0u32)] {
        let motive = Expr::lam(clean_kernel::BinderInfo::Default, p_ty.clone(), nat.clone());
        let minor = Expr::lam(
            clean_kernel::BinderInfo::Default,
            nat.clone(),
            Expr::lam(
                clean_kernel::BinderInfo::Default,
                nat.clone(),
                Expr::bvar(pick),
            ),
        );
        let rec = Expr::const_(
            name("K1Lib.P.rec"),
            vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
        );
        let body = Expr::apps(rec, [motive, minor, Expr::bvar(0)]);
        constant_mut(p, &name(field)).value = Some(Expr::lam(
            clean_kernel::BinderInfo::Default,
            p_ty.clone(),
            body,
        ));
    }
}

/// Y2: the table reversed and both projection constants removed.
fn reverse_table_without_projections(p: &mut CleanPayload) {
    reverse_table(p);
    p.constants
        .retain(|c| c.name != name("K1Lib.P.x") && c.name != name("K1Lib.P.y"));
}

fn assert_inconsistent_at_import(dir: &Path) {
    let mut env = builder_base().0;
    let err = clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(dir))
        .expect_err("an artifact that contradicts itself must refuse the import");
    assert!(err.is_inconsistent_artifact(), "{err}");
}

#[test]
fn recursor_bodied_projections_cannot_carry_a_reversed_table() {
    let tmp = tempfile::tempdir().expect("tmp");
    // Control: the rewritten projections alone (table honest) are the
    // artifact's honest meaning and load.
    let honest = built_lib(tmp.path(), "honest", STRUCT_LIB);
    tamper(&honest, "K1Lib", |p| {
        reverse_table_over_recursor_projections(p);
        reverse_table(p); // back to [x, y]
    });
    let mut env = builder_base().0;
    clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(&honest))
        .expect("recursor-bodied projections under the honest table load");
    assert!(struct_table_is(&env, &["x", "y"]));

    let dir = built_lib(tmp.path(), "lib", STRUCT_LIB);
    tamper(&dir, "K1Lib", reverse_table_over_recursor_projections);
    assert_inconsistent_at_import(&dir);
    let result = struct_project_after_tamper(
        tmp.path(),
        "proj",
        STRUCT_USE_FALSE,
        reverse_table_over_recursor_projections,
    );
    let failure = result
        .failed
        .iter()
        .find(|(m, _)| m == "K1Use")
        .unwrap_or_else(|| panic!("K1Use.px : (P.mk 0 1).x = 1 must not build: {result:?}"));
    assert!(failure.1.contains("inconsistent artifact"), "{failure:?}");
}

#[test]
fn a_reversed_table_with_no_projections_is_refused_at_import() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", STRUCT_LIB);
    tamper(&dir, "K1Lib", reverse_table_without_projections);
    assert_inconsistent_at_import(&dir);
    let result = struct_project_after_tamper(
        tmp.path(),
        "proj",
        STRUCT_USE_FALSE,
        reverse_table_without_projections,
    );
    assert!(
        result.failed.iter().any(|(m, _)| m == "K1Use"),
        "K1Use.px : (P.mk 0 1).x = 1 must not build: {result:?}"
    );
}

/// Y5: a second `K1Lib.v := 1` appended after the honest `:= 0`. Measured on
/// `e3f696689`: the payload loaded, the later record won, and `K1Lib.v = 1`
/// passed check and export-cert.
#[test]
fn a_payload_declaring_a_name_twice_is_refused_at_import() {
    const DEF_LIB: &str = "def K1Lib.v : Nat := 0\n";
    let tmp = tempfile::tempdir().expect("tmp");
    let donor = built_lib(tmp.path(), "donor", "def K1Lib.v : Nat := 1\n");
    let one = read_payload(&olean(&donor, "K1Lib"))
        .1
        .constants
        .into_iter()
        .find(|c| c.name == name("K1Lib.v"))
        .expect("donor K1Lib.v");
    for (tag, append) in [("after", true), ("before", false)] {
        let dir = built_lib(tmp.path(), tag, DEF_LIB);
        let one = one.clone();
        tamper(&dir, "K1Lib", move |p| {
            if append {
                p.constants.push(one);
            } else {
                p.constants.insert(0, one);
            }
        });
        assert_inconsistent_at_import(&dir);
    }
}

/// A declaration carried by an UNRELATED module, imported before its own:
/// `Z`'s payload also declares `K1Lib.v := 1`. Measured on `e3f696689` and
/// `3f45fb7c6`: the first one loaded was kept and `K1Lib.v = 1` passed.
///
/// Round 29: only the duplicate Lean's import allows stands — a theorem of
/// the same statement (measured with `lean` v4.30.0-rc2: two theorems of one
/// statement import; two identical `def`s do not, "environment already
/// contains"). Round 28's control, an identical `def` re-declared by `Z`,
/// loaded; it is refused now, and the control is the theorem.
#[test]
fn a_declaration_another_artifact_declared_differently_is_refused_at_import() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = "def K1Lib.v : Nat := 0
theorem K1Lib.t : 1 = 1 := rfl
";
    let donor = built_lib(
        tmp.path(),
        "donor",
        "def K1Lib.v : Nat := 1
theorem K1Lib.t : 1 = 1 := Eq.refl 1
",
    );
    let genuine = built_lib(tmp.path(), "genuine", lib);
    let donated = |dir: &Path, n: &str| {
        read_payload(&olean(dir, "K1Lib"))
            .1
            .constants
            .into_iter()
            .find(|c| c.name == name(n))
            .unwrap_or_else(|| panic!("{n}"))
    };
    for (tag, carried, refused) in [
        ("conflict", donated(&donor, "K1Lib.v"), true),
        ("same-def", donated(&genuine, "K1Lib.v"), true),
        ("same-statement", donated(&donor, "K1Lib.t"), false),
    ] {
        let dir = tmp.path().join(tag);
        write_project(
            &dir,
            &["K1Lib", "Z"],
            &[
                ("K1Lib", lib),
                (
                    "Z",
                    "def Z.z : Nat := 5
",
                ),
            ],
        );
        assert!(build(&dir).failed.is_empty(), "{tag}: fixture builds");
        tamper(&dir, "Z", move |p| p.constants.push(carried));
        let mut env = builder_base().0;
        clean_olean::load_module_with_deps(&mut env, "Z", &load_paths(&dir)).expect("Z loads");
        let second = clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(&dir));
        if refused {
            let err = second.expect_err("a second declaration must refuse the import");
            assert!(
                matches!(err, clean_olean::ImportError::ConflictingDeclaration { .. }),
                "{tag}: {err}"
            );
        } else {
            second.expect("a second proof of one statement is the same theorem");
        }
    }
}

/// C1 (module-trust round 29): `K1Lib.v := Nat.succ K1Lib.v` in the payload.
/// Measured on `6d4100991`: the artifact loaded and `clean check` of
/// `K1Lib.v = Nat.succ K1Lib.v := rfl` never returned (`reduce_nat` unfolding
/// `K1Lib.v` forever), before any re-check could refuse it. A declaration
/// that depends on itself is refused at import, a chain is not.
#[test]
fn a_definition_that_depends_on_itself_is_refused_at_import() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = "def K1Lib.v : Nat := 0\ndef K1Lib.pid (x : Nat) : Nat := x\n";
    let succ = |e: Expr| Expr::app(Expr::const_(name("Nat.succ"), vec![]), e);
    let v = || Expr::const_(name("K1Lib.v"), vec![]);
    let pid = |e: Expr| Expr::app(Expr::const_(name("K1Lib.pid"), vec![]), e);
    let set_v = |p: &mut CleanPayload, value: Expr| {
        let c = p
            .constants
            .iter_mut()
            .find(|c| c.name == name("K1Lib.v"))
            .expect("K1Lib.v");
        c.value = Some(value);
    };
    // Control: a rewritten value that does not mention `K1Lib.v` loads (the
    // re-check, not the import, is what judges it).
    let control = built_lib(tmp.path(), "control", lib);
    tamper(&control, "K1Lib", |p| {
        set_v(p, pid(succ(Expr::const_(name("Nat.zero"), vec![]))))
    });
    let mut env = builder_base().0;
    clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(&control))
        .expect("an acyclic rewrite is not refused at import");

    for (tag, value) in [("direct", succ(v())), ("through-pid", pid(succ(v())))] {
        let dir = built_lib(tmp.path(), tag, lib);
        tamper(&dir, "K1Lib", |p| set_v(p, value));
        let mut env = builder_base().0;
        let err = clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(&dir))
            .expect_err("a definition that depends on itself must refuse the import");
        assert!(
            matches!(err, clean_olean::ImportError::DefinitionalCycle { .. }),
            "{tag}: {err}"
        );
    }
}

/// Lean-built (`lean` v4.30.0-rc2) artifacts, committed under
/// `tests/fixtures/module_trust_lean_built` (see its README): `honest/D`
/// (`D.w := 1`, `D.v := 0`), `other/Z` (`D.v := 1`), and `twice/D`, the
/// honest `D` with its `D.v` record renamed `D.w` (N2r). Measured on
/// `6d4100991`, `e3f696689` and `3f45fb7c6`: `D.v = 1` passed with `Z`
/// imported before `D` (N3; `lean` refuses: "environment already contains
/// 'D.v' from Z"), and `D.w = 0` passed over `twice/D` (N2r). The rule
/// "one name, one declaration" held for Clean payloads only.
fn lean_built(part: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/module_trust_lean_built")
        .join(part)
}

fn load_lean_built(env: &mut Environment, module: &str, part: &Path) -> Result<(), String> {
    let toolchain = clean_olean::pinned_lean_lib_path().expect("checked by the caller");
    clean_olean::load_module_with_deps(env, module, &[part.to_path_buf(), toolchain])
        .map(|_| ())
        .map_err(|e| {
            assert!(
                e.is_inconsistent_artifact(),
                "refused for another reason: {e}"
            );
            e.to_string()
        })
}

fn fresh_env() -> Environment {
    builder_base().0
}

#[test]
fn two_lean_built_artifacts_declaring_one_name_refuse_the_import() {
    // SELF-SKIP OK: needs the repository-pinned Lean toolchain's Init .oleans (elan install outside the tree) to resolve the Lean-built fixtures' imports; the skip prints why.
    if clean_olean::pinned_lean_lib_path().is_none() {
        eprintln!("SKIP: repository-pinned Lean toolchain not found");
        return;
    }
    // Controls: each loads alone, and Init's own realized duplicates
    // (`dite.congr_simp` in two modules) are the same declaration.
    let mut env = fresh_env();
    load_lean_built(&mut env, "D", &lean_built("honest")).expect("honest D loads");
    assert!(env.get_const(&name("D.v")).is_some());
    let mut env = fresh_env();
    load_lean_built(&mut env, "Z", &lean_built("other")).expect("Z loads");

    for (first, second) in [("Z", "D"), ("D", "Z")] {
        let part = |m: &str| lean_built(if m == "D" { "honest" } else { "other" });
        let mut env = fresh_env();
        load_lean_built(&mut env, first, &part(first)).expect("the first loads");
        let err = load_lean_built(&mut env, second, &part(second))
            .expect_err("a second declaration of D.v must refuse the import");
        assert!(err.contains("`D.v`"), "{first} then {second}: {err}");
    }
}

#[test]
fn a_lean_built_artifact_declaring_a_name_twice_is_refused_at_import() {
    // SELF-SKIP OK: needs the repository-pinned Lean toolchain's Init .oleans (elan install outside the tree) to resolve the Lean-built fixture's imports; the skip prints why.
    if clean_olean::pinned_lean_lib_path().is_none() {
        eprintln!("SKIP: repository-pinned Lean toolchain not found");
        return;
    }
    let mut env = fresh_env();
    let err = load_lean_built(&mut env, "D", &lean_built("twice"))
        .expect_err("D.w declared twice must refuse the import");
    assert!(err.contains("`D.w` more than once"), "{err}");
}

/// X1 (module-trust round 30): the parts of ONE Lean-built module disagree.
/// `parts/` is `lean` v4.30.0-rc2's module-system triple for
/// `@[expose] public def D.e : Nat := 1` and `public def D.v : Nat := 0`;
/// `parts_disagree/` is the same triple with `D.olean.private`'s `D.v`
/// record renamed `D.e` (fixture README), so the public part says
/// `D.e := 1` and the private part — which `lean` reads for a non-module
/// consumer, refusing `D.e = 1` and accepting `D.e = 0` — says `D.e := 0`.
/// Measured on `f4af8f11a`, `6d4100991`, `e3f696689` and `3f45fb7c6`:
/// the private record was dropped unread and `D.e = 1 := rfl` passed.
#[test]
fn the_parts_of_one_lean_built_module_stating_a_declaration_differently_refuse_the_import() {
    // SELF-SKIP OK: needs the repository-pinned Lean toolchain's Init .oleans (elan install outside the tree) to resolve the Lean-built fixtures' imports; the skip prints why.
    if clean_olean::pinned_lean_lib_path().is_none() {
        eprintln!("SKIP: repository-pinned Lean toolchain not found");
        return;
    }
    // Control: the honest triple loads, with `D.v`'s value from the
    // private part and `D.e` stated alike by the public and private parts.
    let mut env = fresh_env();
    load_lean_built(&mut env, "D", &lean_built("parts")).expect("honest D loads");
    for n in ["D.e", "D.v"] {
        assert!(
            env.get_const(&name(n)).is_some_and(|c| c.value.is_some()),
            "{n} is a definition"
        );
    }
    let mut env = fresh_env();
    let err = load_lean_built(&mut env, "D", &lean_built("parts_disagree"))
        .expect_err("the parts of D disagree on D.e");
    assert!(err.contains("state `D.e` differently"), "{err}");
}

/// X1 through the public `ParsedModule` loader: the three parts of `D`
/// loaded under the one module name `D` are one artifact, and the same rule
/// holds there (the loader used to drop the private part's `D.e` unread).
#[test]
fn the_parts_of_one_module_loaded_through_the_parsed_path_must_agree() {
    let load = |fixture: &str| -> Result<Environment, clean_olean::ImportError> {
        let parts = clean_olean::parse_module_parts(lean_built(fixture).join("D.olean"))
            .expect("the parts parse");
        assert_eq!(parts.len(), 3, "{fixture}: base, server and private");
        let mut env = fresh_env();
        for (index, part) in parts.iter().enumerate() {
            clean_olean::load_parsed_module_at_index(
                &mut env,
                &part.module,
                Some("D".to_string()),
                index,
            )?;
        }
        Ok(env)
    };
    let env = load("parts").expect("the honest parts agree");
    assert!(env
        .get_const(&name("D.e"))
        .is_some_and(|c| c.value.is_some()));
    let Err(err) = load("parts_disagree") else {
        panic!("the parts disagree on D.e");
    };
    assert!(
        matches!(err, clean_olean::ImportError::PartsDisagree { ref name, .. } if name == "D.e"),
        "{err}"
    );
}

/// N3p: a Clean-built `Z` declaring `D.v := 1`, imported before the
/// Lean-built `D`. Measured on `6d4100991`: `D.v = 1` passed (the payload
/// rule ran only when a payload loaded after the other artifact).
#[test]
fn a_clean_built_declaration_then_a_lean_built_one_refuse_the_import() {
    // SELF-SKIP OK: needs the repository-pinned Lean toolchain's Init .oleans (elan install outside the tree) to resolve the Lean-built fixture's imports; the skip prints why.
    if clean_olean::pinned_lean_lib_path().is_none() {
        eprintln!("SKIP: repository-pinned Lean toolchain not found");
        return;
    }
    let tmp = tempfile::tempdir().expect("tmp");
    for (tag, source, refused) in [
        ("conflict", "def D.v : Nat := 1\n", true),
        ("unrelated", "def Z.z : Nat := 1\n", false),
    ] {
        let dir = tmp.path().join(tag);
        write_project(&dir, &["Z"], &[("Z", source)]);
        assert!(build(&dir).failed.is_empty(), "{tag}: Z builds");
        let mut env = fresh_env();
        clean_olean::load_module_with_deps(&mut env, "Z", &load_paths(&dir)).expect("Z loads");
        let second = load_lean_built(&mut env, "D", &lean_built("honest"));
        if refused {
            let err = second.expect_err("D.v declared by Z and by D must refuse the import");
            assert!(err.contains("`D.v`"), "{err}");
        } else {
            second.expect("D loads after an unrelated Clean-built module");
        }
    }
}

const MARKS_LIB: &str = "namespace N
protected def w : Nat := 3
private def v : Nat := 4
def u : Nat := 5
end N
";

/// A two-module package: `K1Lib` is `MARKS_LIB`, `K1Use` is `use_source`.
fn marks_project(root: &Path, tag: &str, use_source: &str) -> BuildResult {
    let dir = root.join(tag);
    write_project(
        &dir,
        &["K1Lib", "K1Use"],
        &[("K1Lib", MARKS_LIB), ("K1Use", use_source)],
    );
    build(&dir)
}

#[test]
fn protected_and_private_marks_travel_with_the_artifact() {
    // Round-25 verification of 100c3ccca: the artifact carried no
    // `protected` / `private` marks, so a dependent's `open N; w` reached a
    // protected `N.w` and a `private` declaration was nameable from every
    // importer; `clean lake build` built packages Lean 4.8.0 rejects.
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", MARKS_LIB);
    let (_, payload) = read_payload(&olean(&dir, "K1Lib"));
    assert_eq!(payload.protected_decls, vec![name("N.w")], "{payload:?}");
    // Lean's module-local name (G21 brick B4), which the oracle's own
    // artifact carries for `private def v` in `K1Lib`.
    assert_eq!(
        payload.private_decls,
        vec![name("_private.K1Lib.0.N.v")],
        "{payload:?}"
    );

    let result = marks_project(
        tmp.path(),
        "protected",
        "import K1Lib\nopen N\ntheorem K1Use.t : w = 3 := rfl\n",
    );
    assert!(
        result.failed.iter().any(|(m, _)| m == "K1Use"),
        "`open N` must not reach the protected `N.w`: {result:?}"
    );
    let result = marks_project(
        tmp.path(),
        "private",
        "import K1Lib\ntheorem K1Use.t : N.v = 4 := rfl\n",
    );
    assert!(
        result.failed.iter().any(|(m, _)| m == "K1Use"),
        "another module's `private` declaration must not be nameable: {result:?}"
    );
    // Controls: the qualified protected name and a plain member build.
    let result = marks_project(
        tmp.path(),
        "control",
        "import K1Lib\nopen N\ntheorem K1Use.t : N.w = 3 := rfl\ntheorem K1Use.s : u = 5 := rfl\n",
    );
    assert!(result.failed.is_empty(), "{result:?}");
}

#[test]
fn a_mark_on_a_declaration_the_artifact_does_not_carry_is_refused() {
    // A `protected` mark on another module's name would change what an
    // importer's identifiers resolve to.
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", MARKS_LIB);
    tamper(&dir, "K1Lib", |p| p.protected_decls.push(name("Nat.add")));
    let mut env = builder_base().0;
    let err = clean_olean::load_module_with_deps(&mut env, "K1Lib", &load_paths(&dir))
        .expect_err("a foreign mark must refuse the import");
    assert!(
        matches!(
            err,
            clean_olean::ImportError::InconsistentDeclarationMark { .. }
        ),
        "{err}"
    );
}

const INSTANCE_LIB: &str = "class C where
  v : Nat
instance ib : C := ⟨1⟩
instance ic : C := ⟨2⟩
local instance i3 : C := ⟨3⟩
namespace N
scoped instance i5 : C := ⟨5⟩
end N
";

/// A two-module package: `K1Lib` is `INSTANCE_LIB`, `K1Use` is `use_source`.
fn instance_project(root: &Path, tag: &str, use_source: &str) -> BuildResult {
    let dir = root.join(tag);
    write_project(
        &dir,
        &["K1Lib", "K1Use"],
        &[("K1Lib", INSTANCE_LIB), ("K1Use", use_source)],
    );
    build(&dir)
}

fn builds(result: &BuildResult) -> bool {
    result.failed.is_empty() && result.built.iter().any(|m| m == "K1Use")
}

#[test]
fn the_artifact_carries_the_modules_classes_and_instance_entries() {
    // Round-25 verification of fbbb586e0: the artifact carried no class and
    // no instance, so a dependent resolved no instance of an imported class
    // and refused `attribute [-instance] ib` ("does not have [instance]
    // attribute") that `clean check` and Lean 4.8.0 accept.
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built_lib(tmp.path(), "lib", INSTANCE_LIB);
    let (_, payload) = read_payload(&olean(&dir, "K1Lib"));
    assert_eq!(
        payload
            .classes
            .iter()
            .map(|c| c.name.clone())
            .collect::<Vec<_>>(),
        vec![name("C")],
        "{payload:?}"
    );
    // Global entries in the order they were first given; the `local`
    // instance is never exported.
    assert_eq!(
        payload
            .global_instances
            .iter()
            .map(|i| i.name.clone())
            .collect::<Vec<_>>(),
        vec![name("ib"), name("ic")],
        "{payload:?}"
    );
    assert_eq!(
        payload
            .scoped_instances
            .iter()
            .map(|(ns, i)| (ns.clone(), i.name.clone()))
            .collect::<Vec<_>>(),
        vec![(name("N"), name("N.i5"))],
        "{payload:?}"
    );
}

#[test]
fn a_dependent_resolves_imported_instances_as_lean_does() {
    // Every expectation measured on Lean 4.8.0.
    let tmp = tempfile::tempdir().expect("tmp");
    // The newest imported instance: 2.
    assert!(builds(&instance_project(
        tmp.path(),
        "plain",
        "import K1Lib\ntheorem K1Use.t : C.v = 2 := rfl\n"
    )));
    assert!(!builds(&instance_project(
        tmp.path(),
        "plain_false",
        "import K1Lib\ntheorem K1Use.t : C.v = 1 := rfl\n"
    )));
    // Erased and re-added, `ib` keeps its place behind `ic`: 2.
    assert!(builds(&instance_project(
        tmp.path(),
        "readd",
        "import K1Lib\nattribute [-instance] ib\nattribute [instance] ib\ntheorem K1Use.t : C.v = 2 := rfl\n"
    )));
    assert!(!builds(&instance_project(
        tmp.path(),
        "readd_false",
        "import K1Lib\nattribute [-instance] ib\nattribute [instance] ib\ntheorem K1Use.t : C.v = 1 := rfl\n"
    )));
    // The library's `local instance` is not in force here.
    assert!(!builds(&instance_project(
        tmp.path(),
        "local",
        "import K1Lib\ntheorem K1Use.t : C.v = 3 := rfl\n"
    )));
    // The scoped instance is in force once `N` is opened: 5.
    assert!(builds(&instance_project(
        tmp.path(),
        "scoped",
        "import K1Lib\nopen N\ntheorem K1Use.t : C.v = 5 := rfl\n"
    )));
    assert!(!builds(&instance_project(
        tmp.path(),
        "scoped_closed",
        "import K1Lib\ntheorem K1Use.t : C.v = 5 := rfl\n"
    )));
}

#[test]
fn a_re_insertion_in_a_dependency_reaches_its_importer() {
    // `K1Mid: attribute [instance 50] ic` lowers `ic` in place; its importer
    // replays that entry and takes `ib` (Lean 4.8.0: 1).
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path().join("chain");
    write_project(
        &dir,
        &["K1Lib", "K1Mid", "K1Use"],
        &[
            ("K1Lib", INSTANCE_LIB),
            ("K1Mid", "import K1Lib\nattribute [instance 50] ic\n"),
            ("K1Use", "import K1Mid\ntheorem K1Use.t : C.v = 1 := rfl\n"),
        ],
    );
    let result = build(&dir);
    assert!(result.failed.is_empty(), "{result:?}");
    let (_, payload) = read_payload(&olean(&dir, "K1Mid"));
    assert_eq!(
        payload
            .global_instances
            .iter()
            .map(|i| (i.name.clone(), i.priority))
            .collect::<Vec<_>>(),
        vec![(name("ic"), 50)],
        "{payload:?}"
    );
}

#[test]
fn two_imports_declaring_one_name_are_refused() {
    // `K1P` and `K1Q` each declare `instance : OfNat W n`, which Clean names
    // `instOfNatW` in both. `clean lake build` kept the first import's
    // declaration and, once instances travelled with the artifact, built
    // `(0 : W).x = 3`. Lean 4.8.0 never gives 3 here: inside a package
    // (`L.P`, `L.Q`) both are `instOfNatW` and the import fails
    // ("environment already contains 'instOfNatW._cstage2' from L.P",
    // round-25 lake battery `L_ofnatPQ_3`); for these root modules it names
    // them apart (`instOfNatW_k1P`, `instOfNatW_k1Q`) and takes Q's, 2.
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path().join("clash");
    write_project(
        &dir,
        &["K1B", "K1P", "K1Q", "K1Use"],
        &[
            ("K1B", "structure W where\n  x : Nat\n"),
            ("K1P", "import K1B\ninstance : OfNat W n := ⟨⟨3⟩⟩\n"),
            ("K1Q", "import K1B\ninstance : OfNat W n := ⟨⟨2⟩⟩\n"),
            (
                "K1Use",
                "import K1P\nimport K1Q\ntheorem K1Use.t : (0 : W).x = 3 := rfl\n",
            ),
        ],
    );
    let result = build(&dir);
    assert!(
        result.failed.iter().any(|(m, _)| m == "K1Use"),
        "a clash between two imports must refuse the importer: {result:?}"
    );
    // Control: one of the two imported alone builds.
    let dir = tmp.path().join("single");
    write_project(
        &dir,
        &["K1B", "K1P", "K1Use"],
        &[
            ("K1B", "structure W where\n  x : Nat\n"),
            ("K1P", "import K1B\ninstance : OfNat W n := ⟨⟨3⟩⟩\n"),
            (
                "K1Use",
                "import K1P\ntheorem K1Use.t : (0 : W).x = 3 := rfl\n",
            ),
        ],
    );
    let result = build(&dir);
    assert!(result.failed.is_empty(), "{result:?}");
}
