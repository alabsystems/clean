// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.14 keep-ratchets over the two-language proof program's Lean battery
//! (F-108, F-109), run through the exact `clean compile --emit obj` lowering.
//!
//! The battery is the 20 `GENERAL.*` roots of the 2026-09-17 proof program
//! (`parta-lean/probes/p01..p15,p20`), inlined verbatim below so the ratchet
//! does not depend on a sibling checkout. Both findings were measured through
//! a stale checkout and are closed at the current tree; these tests keep them
//! closed:
//!
//! * **F-108** — every root LOWERS through the `--emit obj` config. Lowering
//!   runs the emitter's finalization gate (`validate_module`), which refused
//!   the old `() -> ()` placeholder `FnDef` with `ConstTypeMismatch`; the
//!   module then round-trips byte-exactly through the v41 module codec. (The
//!   constant-level `FnDef` census and its `ConstTypeMismatch` negative twin
//!   live beside the emitter, in `clean-compiler`'s `emit_trust_ir_tests.rs`.)
//! * **F-109** — the census LINK oracle: an emitted object leaves exactly its
//!   bodyless declarations for the link to resolve, the runtime defines only
//!   `clean_*`, so every bodyless `l_*` declaration must be DEFINED by the
//!   `native_build` prelude shim tables — zero undefined `l_*` symbols across
//!   the battery. Checked by name over the modules' declarations AND by a real
//!   `cc` link of a stand-in object retaining that whole `l_*` demand against
//!   Clean's runtime + runtime_extern + the compiled shim object (the
//!   `trustcg_census.rs` step-3 link inputs). The stand-in retains the
//!   modules' `clean_*` runtime imports too, so the runtime half of the
//!   link demand binds as well, and a bodyless declaration of any third kind
//!   fails the lowering step. Linking is not calling: each `l_*` declaration
//!   is also checked against its shim's C signature (arity, pointer slots),
//!   because a shim defined at the wrong arity links cleanly.
//! * **`GENERAL.link.no_shims`** — the proof program's negative control,
//!   ported by row name: without the shims the linker refuses `sumTo`'s whole
//!   `l_*` demand (`l_Nat_add` among it).
//! * The same step on real trust-cg objects is opt-in
//!   (`CLEAN_TRUSTCG_CENSUS=1`, the census gate leg's switch). Today it is a
//!   GAP ratchet: a v41-aware trust-cg refuses every Clean body because Clean
//!   stamps it `body_gate: ungated` (the fail-closed codegen license), so no
//!   battery object reaches the link. That refusal is asserted exactly and is
//!   never bypassed by relabelling the gate.
//!
//! MUTATION CONTROL: drop `l_UInt64_ofNat`'s DEFINITION from the link input
//! while the lowering's denylist is untouched — the oracle must name exactly
//! that symbol, for exactly the roots that reference it.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use clean_compiler::cli::{CompileArgs, EmitFormat};
use clean_compiler::emit_trust_ir::{
    deserialize_module_bytes, serialize_module_bytes, serialize_tmbc,
};
use clean_compiler::pass_manager::compile_lcnf_to_trust_ir;

use super::{find_trust_cg, host_trust_cg_target, object_emit_config, select_lcnf_decl};
use crate::native_build::link_probe::{linker_undefined, retaining_driver};
use crate::native_build::{
    prelude_shim_definitions, prelude_shim_symbols, prelude_shims_translation_unit,
};

/// `(probe, Lean source, roots)` — `parta-lean/probes/*.lean`, verbatim.
const BATTERY: &[(&str, &str, &[&str])] = &[
    (
        "p01_bool_result",
        "def isLt (a b : UInt64) : Bool := a < b\n",
        &["isLt"],
    ),
    (
        "p02_if_select",
        "def min2 (a b : UInt64) : UInt64 := if a < b then a else b\n",
        &["min2"],
    ),
    (
        "p03_let",
        "def sqLet (a : UInt64) : UInt64 := let t := a + 1; t * t\n",
        &["sqLet"],
    ),
    (
        "p04_nat_structural_rec",
        "def sumTo : Nat → Nat\n  | 0 => 0\n  | n + 1 => (n + 1) + sumTo n\n",
        &["sumTo"],
    ),
    (
        "p05_nat_wf_rec",
        "-- well-founded (fuelled) recursion over Nat; shape of battery row r03\n\
         def gcdF (f a b : Nat) : Nat := if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a\n\
         termination_by f\n",
        &["gcdF"],
    ),
    (
        "p06_inductive_match",
        "inductive Shape where\n  | sq (s : UInt64)\n  | rect (w h : UInt64)\n\n\
         def area : Shape → UInt64\n  | .sq s => s * s\n  | .rect w h => w * h\n\n\
         def areaOfRect (w h : UInt64) : UInt64 := area (.rect w h)\n",
        &["area", "areaOfRect"],
    ),
    (
        "p07_structure",
        "structure Pt where\n  x : UInt64\n  y : UInt64\n\n\
         def dot (p q : Pt) : UInt64 := p.x * q.x + p.y * q.y\n\
         def dotOf (a b c d : UInt64) : UInt64 := dot ⟨a, b⟩ ⟨c, d⟩\n",
        &["dotOf"],
    ),
    (
        "p08_string",
        "def greet (s : String) : String := s ++ \"!\"\n\
         def greetLen (n : UInt64) : Nat := (greet \"hello\").length\n",
        &["greetLen"],
    ),
    (
        "p09_array_list",
        "def sumList : List UInt64 → UInt64\n  | [] => 0\n  | x :: xs => x + sumList xs\n\
         def sumThree (a b c : UInt64) : UInt64 := sumList [a, b, c]\n\
         def arrSize (a b : UInt64) : Nat := (#[a, b, a]).size\n",
        &["sumThree", "arrSize"],
    ),
    (
        "p10_closure_higher_order",
        "def applyTwice (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f (f x)\n\
         def addK (k x : UInt64) : UInt64 := applyTwice (fun y => y + k) x\n",
        &["applyTwice", "addK"],
    ),
    (
        "p11_typeclass_instance",
        "class Scale (α : Type) where\n  scale : α → α\n\n\
         instance instScaleU64 : Scale UInt64 where\n  scale := fun (x : UInt64) => x * 3\n\n\
         def triple (x : UInt64) : UInt64 := @Scale.scale UInt64 instScaleU64 x\n",
        &["triple"],
    ),
    (
        "p12_mixed_widths",
        "def w8 (a b : UInt8) : UInt8 := a * b + 1\n\
         def w16 (a b : UInt16) : UInt16 := a - b\n\
         def w32 (a b : UInt32) : UInt32 := a + b * a\n\
         def pickWide (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64) : UInt16 := b\n",
        &["w8", "w32"],
    ),
    (
        "p13_division",
        "def quot (a b : UInt64) : UInt64 := a / b\n",
        &["quot"],
    ),
    (
        "p14_lean_to_lean_call",
        "def inc (a : UInt64) : UInt64 := a + 1\n\
         def inc2 (a : UInt64) : UInt64 := inc (inc a)\n",
        &["inc2"],
    ),
    (
        "p15_bitwise",
        "def mask (a b : UInt64) : UInt64 := (a &&& b) ||| 1\n",
        &["mask"],
    ),
    (
        "p20_bool_connective",
        "-- Bool connective over two comparisons (DESIGN Part A: \"Bool comparison + connective\")\n\
         def both (a b c : UInt64) : Bool := a < b && b < c\n",
        &["both"],
    ),
];

/// The mutation-control symbol: F-109's headline shim.
const MUTATED_SHIM: &str = "l_UInt64_ofNat";

/// The battery roots whose `--emit obj` module declares `l_UInt64_ofNat`,
/// measured at this tree. Pinned exactly, so the control's reach cannot
/// silently shrink (or the oracle go quiet) without this list changing in
/// review.
///
/// Measured 2026-09-18: six roots. The archive's stale-checkout run recorded
/// `undefined ['l_UInt64_ofNat']` for more (`area`, `areaOfRect`, `dotOf`,
/// `addK` too); at this tree their `--emit obj` modules carry no such
/// declaration, so the mutation does not reach them.
const ROOTS_REFERENCING_MUTATED_SHIM: &[&str] =
    &["inc2", "mask", "quot", "sqLet", "sumThree", "triple"];

/// One lowered battery root: its source dir (kept alive), args, the bodyless
/// `l_*` declarations its module leaves for the link, and its tMBC bytes.
struct LoweredRoot {
    root: &'static str,
    _dir: tempfile::TempDir,
    externs: BTreeSet<String>,
    tmbc: Vec<u8>,
    /// Every bodyless `clean_*` runtime import the module declares: the other
    /// half of what the link must resolve (Clean's runtime defines these).
    runtime_imports: BTreeSet<String>,
    /// The declared ABI of each `l_*` extern, for the shim-signature check.
    extern_abis: BTreeMap<String, ExternAbi>,
}

/// A bodyless declaration's lowered signature, as the module states it
/// (`Debug` spellings of the trust-ir types: this crate does not name them).
#[derive(Clone, Debug, PartialEq, Eq)]
struct ExternAbi {
    params: Vec<String>,
    returns: Vec<String>,
    vararg: bool,
}

fn args_for(file: &Path, root: &str) -> CompileArgs {
    CompileArgs {
        file: Some(file.to_path_buf()),
        decl: Some(root.to_owned()),
        emit: EmitFormat::Obj,
        opt_level: 0,
        output: None,
        link_artifact: Vec::new(),
    }
}

/// The lowered battery, shared by every test in this module: lowering the 20
/// roots re-elaborates each probe against the prelude and dominates the
/// module's wall time, and the result is immutable.
fn lowered_battery() -> &'static [LoweredRoot] {
    static LOWERED: OnceLock<Vec<LoweredRoot>> = OnceLock::new();
    LOWERED.get_or_init(lower_battery)
}

/// Lower every battery root exactly as `compile_to_object` does (same decl
/// selection, same [`object_emit_config`]), asserting F-108's closure: each
/// module passes the emitter's finalization gate and round-trips byte-exactly.
fn lower_battery() -> Vec<LoweredRoot> {
    let mut lowered = Vec::new();
    for (probe, source, roots) in BATTERY {
        for root in *roots {
            let dir = tempfile::tempdir().expect("tempdir");
            let file = dir.path().join(format!("{probe}.lean"));
            std::fs::write(&file, source).expect("write probe");
            let args = args_for(&file, root);
            let (decls, env, pipeline) = select_lcnf_decl(&args)
                .unwrap_or_else(|e| panic!("{probe}.{root}: selection failed: {e:#}"));
            let module =
                compile_lcnf_to_trust_ir(&decls, &env, &pipeline, &object_emit_config(&args))
                    .unwrap_or_else(|e| {
                        panic!("{probe}.{root}: the --emit obj lowering refused: {e}")
                    });
            let bytes =
                serialize_module_bytes(&module).expect("lowered module has a wire identity");
            let decoded = deserialize_module_bytes(&bytes)
                .unwrap_or_else(|e| panic!("{probe}.{root}: own bytes do not decode: {e}"));
            assert_eq!(
                serialize_module_bytes(&decoded).expect("decoded module has a wire identity"),
                bytes,
                "{probe}.{root}: module must round-trip byte-exactly"
            );
            assert!(
                module
                    .functions
                    .iter()
                    .any(|f| f.name == *root && !f.blocks.is_empty()),
                "{probe}.{root}: the root must be DEFINED in its own module"
            );
            let externs = module
                .functions
                .iter()
                .filter(|f| f.blocks.is_empty() && f.name.starts_with("l_"))
                .map(|f| f.name.clone())
                .collect();
            let mut runtime_imports = BTreeSet::new();
            let mut extern_abis = BTreeMap::new();
            for f in module.functions.iter().filter(|f| f.blocks.is_empty()) {
                // Fail closed on a third kind of link demand: the oracle below
                // resolves `l_*` against the shims and `clean_*` against the
                // runtime, and nothing else would be resolved at all.
                if f.name.starts_with("l_") {
                    let ft = &module.func_types[f.ty.index() as usize];
                    extern_abis.insert(
                        f.name.clone(),
                        ExternAbi {
                            params: ft.params.iter().map(|t| format!("{t:?}")).collect(),
                            returns: ft.returns.iter().map(|t| format!("{t:?}")).collect(),
                            vararg: ft.is_vararg,
                        },
                    );
                } else if f.name.starts_with("clean_") {
                    runtime_imports.insert(f.name.clone());
                } else {
                    panic!(
                        "{probe}.{root}: bodyless declaration `{}` is neither a prelude \
                         shim (`l_*`) nor a runtime import (`clean_*`): nothing the \
                         census links would define it",
                        f.name
                    );
                }
            }
            lowered.push(LoweredRoot {
                runtime_imports,
                extern_abis,
                root,
                _dir: dir,
                externs,
                tmbc: serialize_tmbc(&module).expect("lowered module has a wire identity"),
            });
        }
    }
    assert_eq!(lowered.len(), 20, "the battery is 20 roots");
    lowered
}

/// The toolchain-free LINK oracle: per root, the `l_*` declarations no
/// linked shim defines.
fn undefined_by_declarations(
    lowered: &[LoweredRoot],
    omit: &[&str],
) -> BTreeMap<&'static str, Vec<String>> {
    let defined: BTreeSet<&str> = prelude_shim_symbols()
        .into_iter()
        .filter(|s| !omit.contains(s))
        .collect();
    lowered
        .iter()
        .filter_map(|r| {
            let missing: Vec<String> = r
                .externs
                .iter()
                .filter(|s| !defined.contains(s.as_str()))
                .cloned()
                .collect();
            (!missing.is_empty()).then_some((r.root, missing))
        })
        .collect()
}

/// POSITIVE + MUTATION CONTROL, both LINK oracles over the lowered battery.
///
/// (a) Declarations: zero undefined `l_*` against the full shim union; with
///     `l_UInt64_ofNat`'s definition dropped, exactly the pinned roots report
///     exactly that symbol.
/// (b) A real `cc` link: a stand-in object that references EVERY symbol the
///     battery's modules leave for the link — each `l_*` extern AND each
///     `clean_*` runtime import — is linked against the runtime,
///     runtime_extern and the compiled shim object, so the shims and the
///     runtime are shown to DEFINE those symbols as the linker sees them,
///     not merely to list their names. Dropping `l_UInt64_ofNat` from the
///     shim object makes the linker name exactly that symbol.
#[test]
fn trust_ir_battery_census_link_oracle() {
    let lowered = lowered_battery();

    let undefined = undefined_by_declarations(lowered, &[]);
    assert!(
        undefined.is_empty(),
        "battery roots leave `l_*` symbols no native_build shim defines: {undefined:?}"
    );
    let mutated = undefined_by_declarations(lowered, &[MUTATED_SHIM]);
    let reached: Vec<&str> = mutated.keys().copied().collect();
    assert_eq!(
        reached, ROOTS_REFERENCING_MUTATED_SHIM,
        "the mutation must reach exactly the pinned roots"
    );
    for (root, missing) in &mutated {
        assert_eq!(
            missing,
            &[MUTATED_SHIM.to_owned()],
            "{root}: the oracle must name exactly the dropped shim"
        );
    }

    let demand = battery_link_demand(lowered);
    assert!(
        demand.contains(MUTATED_SHIM),
        "the battery no longer demands `{MUTATED_SHIM}`: {demand:?}"
    );
    let cc = census_cc();
    assert_eq!(
        link_standin(&cc, &demand, &[]),
        BTreeSet::new(),
        "the linker leaves battery `l_*` demand undefined against the full shim object"
    );
    assert_eq!(
        link_standin(&cc, &demand, &[MUTATED_SHIM]),
        BTreeSet::from([MUTATED_SHIM.to_owned()]),
        "the linker must name exactly the dropped shim"
    );
}

/// Everything the battery's modules leave for the link: each `l_*` extern
/// (the shims' half) and each `clean_*` runtime import (the runtime's half).
/// A trust-cg object calls both kinds as undefined external symbols, so the
/// census step-3 link must resolve both — retaining only the `l_*` half
/// would pass a module that imports a runtime entry point Clean's runtime
/// no longer defines.
fn battery_link_demand(lowered: &[LoweredRoot]) -> BTreeSet<String> {
    lowered
        .iter()
        .flat_map(|r| r.externs.iter().chain(&r.runtime_imports).cloned())
        .collect()
}

/// WS6.14 review (adversarial): the runtime half of the link demand binds.
/// The battery's whole demand plus ONE runtime import Clean's runtime does
/// not define (`clean_ws614_absent`, standing in for an emitter that starts
/// importing an entry point the runtime dropped) is refused by the linker,
/// which names exactly that symbol — the census cannot pass it for want of
/// retaining it.
#[test]
fn trust_ir_battery_census_link_oracle_binds_runtime_imports() {
    let lowered = lowered_battery();
    let imports: BTreeSet<&String> = lowered.iter().flat_map(|r| &r.runtime_imports).collect();
    for needed in [
        "clean_alloc_closure",
        "clean_apply_1",
        "clean_inc",
        "clean_dec",
    ] {
        assert!(
            imports.iter().any(|s| s.as_str() == needed),
            "the battery no longer imports `{needed}` (census lost its runtime subject): {imports:?}"
        );
    }
    let mut demand = battery_link_demand(lowered);
    demand.insert("clean_ws614_absent".to_owned());
    assert_eq!(
        link_standin(&census_cc(), &demand, &[]),
        BTreeSet::from(["clean_ws614_absent".to_owned()]),
        "the linker must name exactly the runtime import nothing defines"
    );
}

/// The ABI a shim's C definition states for `symbol`: its parameter C types
/// and its return C type, read from the definition's first declarator.
fn shim_c_signature(symbol: &str, definition: &str) -> Option<(Vec<String>, String)> {
    let at = definition.find(&format!("{symbol}("))?;
    let ret = definition[..at]
        .trim()
        .trim_start_matches("static ")
        .trim()
        .to_owned();
    let open = at + symbol.len() + 1;
    let close = open + definition[open..].find(')')?;
    let params: Vec<String> = definition[open..close]
        .split(',')
        .map(|p| p.split_whitespace().collect::<Vec<_>>().join(" "))
        .filter(|p| !p.is_empty() && p != "void")
        .collect();
    Some((params, ret))
}

/// Why `definition` (the shim for `symbol`) cannot be what a module declaring
/// `abi` calls, or `None` when it is: same arity, no varargs, and every
/// trust-ir `Ptr` slot a C pointer. The census only admits the all-`Ptr`
/// boxed ABI every battery extern uses today; any other declared type is
/// reported, never waved through.
fn shim_abi_mismatch(symbol: &str, definition: &str, abi: &ExternAbi) -> Option<String> {
    let Some((params, ret)) = shim_c_signature(symbol, definition) else {
        return Some(format!(
            "{symbol}: the shim definition has no `{symbol}(` declarator"
        ));
    };
    if abi.vararg {
        return Some(format!("{symbol}: declared vararg; no shim is variadic"));
    }
    if params.len() != abi.params.len() {
        return Some(format!(
            "{symbol}: declared with {} parameter(s), the shim defines {}",
            abi.params.len(),
            params.len()
        ));
    }
    let ptr = |c: &str| c.contains('*');
    for (i, (decl, c)) in abi.params.iter().zip(&params).enumerate() {
        if decl != "Ptr" || !ptr(c) {
            return Some(format!(
                "{symbol}: parameter {i} declared `{decl}`, the shim takes `{c}`"
            ));
        }
    }
    if abi.returns != ["Ptr"] || !ptr(&ret) {
        return Some(format!(
            "{symbol}: declared returning {:?}, the shim returns `{ret}`",
            abi.returns
        ));
    }
    None
}

/// WS6.14 review (adversarial): a shim that DEFINES the symbol at the wrong
/// arity links cleanly and then reads garbage argument registers — the link
/// oracle cannot see it. So every `l_*` extern a battery module declares is
/// checked against its shim's C signature: same arity, pointer slots only.
/// MUTATION CONTROL: `l_HAdd_hAdd`'s real shim with one parameter dropped is
/// refused by name.
#[test]
fn trust_ir_battery_census_shim_abi_matches_declarations() {
    let lowered = lowered_battery();
    let definitions = prelude_shim_definitions();
    let definition_of = |symbol: &str| {
        definitions
            .iter()
            .find(|(s, _)| *s == symbol)
            .map(|(_, d)| *d)
            .unwrap_or_else(|| panic!("no shim defines `{symbol}`"))
    };
    let mut checked = 0usize;
    let mut bad = Vec::new();
    for root in lowered {
        for (symbol, abi) in &root.extern_abis {
            checked += 1;
            if let Some(why) = shim_abi_mismatch(symbol, definition_of(symbol), abi) {
                bad.push(format!("{}: {why}", root.root));
            }
        }
    }
    assert!(
        bad.is_empty(),
        "shim ABI disagrees with the declaration: {bad:?}"
    );
    assert!(checked >= 40, "only {checked} extern declarations checked");

    let hadd = lowered
        .iter()
        .find_map(|r| r.extern_abis.get("l_HAdd_hAdd"))
        .expect("the battery declares `l_HAdd_hAdd`");
    assert_eq!(hadd.params.len(), 6, "the typeclass-projection ABI");
    let real = definition_of("l_HAdd_hAdd");
    let (params, _) = shim_c_signature("l_HAdd_hAdd", real).expect("declarator");
    let dropped = real.replacen(&format!("{}, ", params[0]), "", 1);
    assert_eq!(
        shim_abi_mismatch("l_HAdd_hAdd", &dropped, hadd),
        Some("l_HAdd_hAdd: declared with 6 parameter(s), the shim defines 5".to_owned()),
        "a 5-parameter shim for a 6-parameter declaration must be refused by name"
    );
}

/// Proof-program row `GENERAL.link.no_shims` (F-131's measured negative
/// control, the twin of every `GENERAL.*.linkrun` row): `sumTo` linked
/// against Clean's runtime WITHOUT the prelude shims is REFUSED by the
/// linker, which names `l_Nat_add`. Ported here so the LINK oracle's positive
/// half above cannot pass because the link inputs stopped mattering: with
/// every shim definition dropped, the linker must report exactly `sumTo`'s
/// whole `l_*` demand undefined.
///
/// RATCHET: the archived harness records this row as `REFUSED`; it reads
/// `PASS` once WS8 (F-120) teaches the harness that a reproduced negative
/// control is a pass. The in-repo verdict is the refusal itself.
#[test]
fn general_link_no_shims() {
    let lowered = lowered_battery();
    let sum_to = lowered
        .iter()
        .find(|r| r.root == "sumTo")
        .expect("the battery lowers `sumTo`");
    assert!(
        sum_to.externs.contains("l_Nat_add"),
        "`sumTo` no longer demands `l_Nat_add`: {:?}",
        sum_to.externs
    );
    let every_shim = prelude_shim_symbols();
    let cc = census_cc();
    assert_eq!(
        link_standin(&cc, &sum_to.externs, &every_shim),
        sum_to.externs,
        "without the prelude shims the linker must refuse `sumTo`'s whole `l_*` demand, by name"
    );
    assert_eq!(
        link_standin(&cc, &sum_to.externs, &[]),
        BTreeSet::new(),
        "control: with the shims the same link succeeds"
    );
}

// ---------------------------------------------------------------------------
// Link plumbing (the `trustcg_census.rs` step-3 shape).
// ---------------------------------------------------------------------------

fn census_cc() -> String {
    ["cc", "gcc", "clang"]
        .into_iter()
        .find(|cc| {
            Command::new(cc)
                .arg("--version")
                .output()
                .is_ok_and(|o| o.status.success())
        })
        .expect("the census LINK oracle needs a C compiler (cc, gcc or clang)")
        .to_owned()
}

/// Materialize the runtime header, runtime, runtime_extern and the shim TU
/// (minus `omit`) in `dir`, flattening the crate-relative header include.
fn materialize_link_inputs(dir: &Path, omit: &[&str]) -> Vec<PathBuf> {
    std::fs::write(dir.join("clean_runtime.h"), clean_runtime::runtime_header())
        .expect("write header");
    let flat = |src: &str| src.replacen("../include/clean_runtime.h", "clean_runtime.h", 1);
    let files = [
        ("clean_runtime.c", flat(clean_runtime::runtime_source())),
        (
            "runtime_extern.c",
            flat(clean_runtime::runtime_extern_source()),
        ),
        ("shims.c", prelude_shims_translation_unit(omit)),
    ];
    files
        .into_iter()
        .map(|(name, text)| {
            let path = dir.join(name);
            std::fs::write(&path, text).expect("write link input");
            path
        })
        .collect()
}

/// Link `objects` + `driver` against the runtime and the shim TU minus
/// `omit`. Returns the symbols the linker reports undefined (empty on a
/// successful link); a link failure that names no undefined symbol panics
/// with the linker's stderr, so a broken shim TU cannot read as a pass.
fn link_against_runtime(
    cc: &str,
    dir: &Path,
    driver: &Path,
    objects: &[PathBuf],
    omit: &[&str],
) -> BTreeSet<String> {
    let inputs = materialize_link_inputs(dir, omit);
    let link = Command::new(cc)
        .arg("-O0")
        .arg("-I")
        .arg(dir)
        .arg("-o")
        .arg(dir.join("driver"))
        .arg(driver)
        .args(objects)
        .args(&inputs)
        .arg("-lm")
        .output()
        .expect("spawn cc link");
    if link.status.success() {
        return BTreeSet::new();
    }
    let stderr = String::from_utf8_lossy(&link.stderr);
    let undefined = linker_undefined(&stderr);
    assert!(
        !undefined.is_empty(),
        "link failed without naming an undefined symbol:\n{stderr}"
    );
    undefined
}

/// The stand-in link: a driver retaining exactly `demand`.
fn link_standin(cc: &str, demand: &BTreeSet<String>, omit: &[&str]) -> BTreeSet<String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let driver = retaining_driver(dir.path(), demand);
    link_against_runtime(cc, dir.path(), &driver, &[], omit)
}

// ---------------------------------------------------------------------------
// The trust-cg object link (opt-in: CLEAN_TRUSTCG_CENSUS=1).
// ---------------------------------------------------------------------------

/// The named refusal a v41-aware trust-cg gives a body Clean stamps
/// `body_gate: ungated` — every Clean body today, by design (the fail-closed
/// codegen license; WS6 earns `Gated` per function through the kernel TV
/// certificate). Relabelling the gate to get past it would launder the
/// license, so the census does not; it records the refusal instead.
const UNGATED_REFUSAL: &str = "is affirmatively ungated";

fn census_opted_in() -> bool {
    std::env::var("CLEAN_TRUSTCG_CENSUS").is_ok_and(|v| v == "1")
}

/// `TRUSTCG_BIN` (the census leg's variable), else `CLEAN_TRUST_CG_BIN`,
/// else `--emit obj`'s own PATH lookup. A SELECTED path is authoritative: one
/// that is not a file panics instead of falling through to PATH (the WS6.0
/// review measured exactly that fall-through — a relative selection resolved
/// from the repo root but not from the test's cwd, the package root — so the
/// census silently ran a different trust-cg than the one the gate named).
fn census_trust_cg() -> PathBuf {
    for var in ["TRUSTCG_BIN", "CLEAN_TRUST_CG_BIN"] {
        if let Some(selected) = std::env::var_os(var) {
            let path = PathBuf::from(selected);
            assert!(
                path.is_file(),
                "{var}={} is not a file from the test's cwd ({}); pass an absolute path",
                path.display(),
                std::env::current_dir()
                    .map(|d| d.display().to_string())
                    .unwrap_or_default()
            );
            return path;
        }
    }
    find_trust_cg().expect("valid trust-cg selection").expect(
        "CLEAN_TRUSTCG_CENSUS=1 requires trust-cg (TRUSTCG_BIN, CLEAN_TRUST_CG_BIN or PATH)",
    )
}

/// What trust-cg does with one root's `--emit obj` module.
enum Codegen {
    Object(PathBuf),
    LicenseRefused,
}

fn codegen_root(tcg: &Path, dir: &Path, root: &LoweredRoot) -> Codegen {
    let tmbc = dir.join("root.tmbc");
    let obj = dir.join("root.o");
    std::fs::write(&tmbc, &root.tmbc).expect("write tmbc");
    let target = host_trust_cg_target().expect("trust-cg host target");
    let cg = Command::new(tcg)
        .args(["-c", "--target", target, "-o"])
        .arg(&obj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    if cg.status.success() {
        return Codegen::Object(obj);
    }
    let stderr = String::from_utf8_lossy(&cg.stderr);
    assert!(
        stderr.contains(UNGATED_REFUSAL),
        "{}: trust-cg failed for a reason other than the codegen license \
         (a trust-cg too old for v41 reports `unsupported version`):\n{stderr}",
        root.root
    );
    Codegen::LicenseRefused
}

/// The census step 3 on real trust-cg objects. Opted in, every root either
/// links with zero undefined `l_*` (and, for the pinned roots, the linker
/// names exactly `l_UInt64_ofNat` once its definition is dropped), or is
/// refused by the codegen license — never anything else.
///
/// RATCHET (GAP, asserted exactly): today every battery root is refused by
/// the license, because Clean stamps every body `Ungated`. When WS6 earns
/// `Gated` for a root, it moves out of `LICENSE_REFUSED_ROOTS` in the same
/// commit and the link assertions above start to bind it.
#[test]
fn trust_ir_battery_census_trustcg_link() {
    if census_opted_in() {
        trustcg_link_census();
    } else {
        // Not opted in: no trust-cg runs. Say so loudly, and still pin the
        // ratchet's shape so this arm is never an empty pass.
        assert_eq!(
            LICENSE_REFUSED_ROOTS.len(),
            20,
            "the license ratchet must name the whole battery until WS6 earns Gated"
        );
        eprintln!(
            "SKIP trust_ir_battery_census_trustcg_link: set CLEAN_TRUSTCG_CENSUS=1 \
             (and TRUSTCG_BIN) to run the trust-cg census LINK step"
        );
    }
}

/// Battery roots trust-cg refuses with [`UNGATED_REFUSAL`], measured
/// 2026-09-18 with a v41-aware trust-cg (a release build of trust-cg 0.6.0
/// at a v41-reading trust-ir pin): all of them. The aterm-packaged
/// trust-cg 0.6.0 of the same date predates v41 and fails every root with
/// `unsupported version`, which this test reports as a failure rather than
/// counting — point `TRUSTCG_BIN` at a v41 reader.
const LICENSE_REFUSED_ROOTS: &[&str] = &[
    "addK",
    "applyTwice",
    "area",
    "areaOfRect",
    "arrSize",
    "both",
    "dotOf",
    "gcdF",
    "greetLen",
    "inc2",
    "isLt",
    "mask",
    "min2",
    "quot",
    "sqLet",
    "sumThree",
    "sumTo",
    "triple",
    "w32",
    "w8",
];

fn trustcg_link_census() {
    let tcg = census_trust_cg();
    let cc = census_cc();
    let lowered = lowered_battery();

    let mut refused: Vec<&str> = Vec::new();
    for root in lowered {
        let dir = tempfile::tempdir().expect("tempdir");
        let obj = match codegen_root(&tcg, dir.path(), root) {
            Codegen::Object(obj) => obj,
            Codegen::LicenseRefused => {
                refused.push(root.root);
                continue;
            }
        };
        let driver = retaining_driver(dir.path(), &BTreeSet::from([root.root.to_owned()]));
        let objects = [obj];
        assert_eq!(
            link_against_runtime(&cc, dir.path(), &driver, &objects, &[]),
            BTreeSet::new(),
            "{}: undefined symbols against the full shim object",
            root.root
        );
        let expected = if ROOTS_REFERENCING_MUTATED_SHIM.contains(&root.root) {
            BTreeSet::from([MUTATED_SHIM.to_owned()])
        } else {
            BTreeSet::new()
        };
        assert_eq!(
            link_against_runtime(&cc, dir.path(), &driver, &objects, &[MUTATED_SHIM]),
            expected,
            "{}: the linker must name exactly the dropped shim, and only where referenced",
            root.root
        );
    }
    refused.sort_unstable();
    assert_eq!(
        refused, LICENSE_REFUSED_ROOTS,
        "the codegen-license ratchet moved: update LICENSE_REFUSED_ROOTS in the \
         commit that earns (or loses) a root's license"
    );
}

// WS6.3 (F-105): the battery's `mask` runs, and the census of the bitwise
// shims — a child module so this gate leg's filter selects it.
#[path = "compile_ws6_3_tests.rs"]
mod ws6_3;

// WS6.10 (F-107): the p12b width-conversion probe and the review's
// real-pipeline conversion shapes — a child module (like `ws6_3`) so this
// gate leg's filter selects it and this file stays under the size ratchet.
#[path = "compile_ws6_10_tests.rs"]
mod ws6_10;

// Rule C1 at every trust-ir door (`--emit trustir`, `trustir-bin`, `obj`): the
// constructor shapes the runtime header cannot hold are refused by name at
// build time — a child module (like `ws6_10`) so this gate leg's filter
// selects it.
#[path = "compile_layout_door_tests.rs"]
mod layout_doors;
