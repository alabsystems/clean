// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Navigation of the decoded `summary`, `library`, and `opaques` segments.
//!
//! Layout references (Coq 8.20):
//! - `vernac/library.ml`: `summary_disk`, `library_disk`
//! - `kernel/safe_typing.ml`: `compiled_library`
//! - `kernel/declarations.mli`: `module_body`, `structure_body`,
//!   `constant_body`, `mutual_inductive_body`
//! - `checker/values.ml`: authoritative field shapes (`v_libsum`, `v_lib`,
//!   `v_compiled_lib`, `v_module`, `v_cb`, `v_ind_pack`, `v_opaquetable`)

use super::marshal_parser::{MValue, MarshalDag};
use super::vo_parser::{VoParseError, VoResult};

fn structure(context: &str, message: impl Into<String>) -> VoParseError {
    VoParseError::Structure {
        context: context.to_string(),
        message: message.into(),
    }
}

fn block<'d>(dag: &'d MarshalDag, v: MValue, ctx: &str) -> VoResult<(u8, &'d [MValue])> {
    dag.block(v)
        .ok_or_else(|| structure(ctx, format!("expected block, got {v:?}")))
}

fn tuple<'d>(dag: &'d MarshalDag, v: MValue, n: usize, ctx: &str) -> VoResult<&'d [MValue]> {
    let (tag, fields) = block(dag, v, ctx)?;
    if tag != 0 || fields.len() != n {
        return Err(structure(
            ctx,
            format!(
                "expected tuple of {n} fields, got tag {tag} with {}",
                fields.len()
            ),
        ));
    }
    Ok(fields)
}

fn string(dag: &MarshalDag, v: MValue, ctx: &str) -> VoResult<String> {
    dag.string_lossy(v)
        .ok_or_else(|| structure(ctx, format!("expected string, got {v:?}")))
}

/// Decode a `DirPath.t` (stored most-local first) to dotted outermost-first.
fn dirpath_dotted(dag: &MarshalDag, v: MValue, ctx: &str) -> VoResult<String> {
    let ids = dag
        .list(v)
        .ok_or_else(|| structure(ctx, "expected DirPath list"))?;
    let mut parts = Vec::with_capacity(ids.len());
    for id in ids.into_iter().rev() {
        parts.push(string(dag, id, ctx)?);
    }
    Ok(parts.join("."))
}

// ---------------------------------------------------------------------------
// Summary segment
// ---------------------------------------------------------------------------

/// Decoded `summary_disk`.
#[derive(Clone, Debug)]
pub struct LibrarySummary {
    /// Logical library name, e.g. "Coq.Init.Logic".
    pub name: String,
    /// Logical names of required libraries.
    pub deps: Vec<String>,
    /// OCaml version string the library was compiled with.
    pub ocaml: String,
}

/// Read the `summary` segment: `{md_name; md_deps; md_ocaml; md_info}`.
///
/// # Errors
///
/// Returns `VoParseError::Structure` if the segment does not have the
/// `summary_disk` shape.
pub fn read_summary(dag: &MarshalDag) -> VoResult<LibrarySummary> {
    let f = tuple(dag, dag.root, 4, "summary_disk")?;
    let name = dirpath_dotted(dag, f[0], "summary md_name")?;
    let deps_arr = dag
        .array(f[1])
        .ok_or_else(|| structure("summary md_deps", "expected array"))?;
    let mut deps = Vec::with_capacity(deps_arr.len());
    for d in deps_arr {
        let df = tuple(dag, *d, 2, "summary dep")?;
        deps.push(dirpath_dotted(dag, df[0], "summary dep name")?);
    }
    let ocaml = string(dag, f[2], "summary md_ocaml")?;
    Ok(LibrarySummary { name, deps, ocaml })
}

// ---------------------------------------------------------------------------
// Library segment
// ---------------------------------------------------------------------------

/// How a constant's body is stored (`constant_def` constructor).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstantDefKind {
    /// Axiom / parameter: no body.
    Undef,
    /// Transparent definition: body inline in the library segment.
    Def,
    /// Qed-opaque definition: body in the `opaques` segment.
    OpaqueDef,
    /// Kernel primitive.
    Primitive,
    /// Rewrite-rule symbol.
    Symbol,
}

/// A constant found in the library structure. `type_val` / `body_val` are
/// handles into the library segment's DAG, decodable with
/// [`super::constr_decode::ConstrDecoder`].
#[derive(Clone, Debug)]
pub struct VoConstant {
    pub label: String,
    pub qualified: String,
    pub def: ConstantDefKind,
    /// `const_type` (a `Constr`).
    pub type_val: MValue,
    /// Inline body for `Def` constants.
    pub body_val: Option<MValue>,
    /// Index into the `opaques` segment table for `OpaqueDef` constants.
    pub opaque_index: Option<i64>,
}

/// A mutual inductive block found in the library structure.
#[derive(Clone, Debug)]
pub struct VoInductiveBlock {
    pub label: String,
    pub qualified: String,
    /// Type names of the block's packets.
    pub type_names: Vec<String>,
    /// Constructor names per packet (kernel order, so constructor `k` here
    /// is 1-based index `k+1` in `Construct` nodes).
    pub ctor_names: Vec<Vec<String>>,
    /// `mind_user_lc` handles per packet (constructor types, `Constr`s).
    pub ctor_type_vals: Vec<Vec<MValue>>,
}

/// Everything extracted from the `library` segment structure walk.
#[derive(Clone, Debug)]
pub struct VoLibraryContent {
    pub constants: Vec<VoConstant>,
    pub inductives: Vec<VoInductiveBlock>,
    /// Qualified names of (sub)modules and module types.
    pub modules: Vec<String>,
}

/// Read the `library` segment: `library_disk` → `compiled_library` →
/// `module_body` → `structure_body`, collecting constants and inductives.
///
/// # Errors
///
/// Returns `VoParseError::Structure` on shape mismatches.
pub fn read_library(dag: &MarshalDag, lib_name: &str) -> VoResult<VoLibraryContent> {
    // library_disk = { md_compiled; md_syntax_objects; md_objects }
    let lib = tuple(dag, dag.root, 3, "library_disk")?;
    // compiled_library = { comp_name; comp_mod; comp_univs; comp_deps; comp_flags }
    let compiled = tuple(dag, lib[0], 5, "compiled_library")?;
    let module = compiled[1];

    let mut out = VoLibraryContent {
        constants: Vec::new(),
        inductives: Vec::new(),
        modules: Vec::new(),
    };
    walk_module(dag, module, lib_name, &mut out, 0)?;
    Ok(out)
}

/// Recursion cap for nested modules (stdlib maxima are single digits).
const MAX_MODULE_DEPTH: usize = 64;

/// Walk a `module_body` (or `module_type_body`): both are 6-field tuples
/// with the signature at index 2.
fn walk_module(
    dag: &MarshalDag,
    module: MValue,
    prefix: &str,
    out: &mut VoLibraryContent,
    depth: usize,
) -> VoResult<()> {
    if depth > MAX_MODULE_DEPTH {
        return Err(structure("module_body", "module nesting too deep"));
    }
    let mf = tuple(dag, module, 6, "module_body")?;
    let sign = mf[2];
    let (tag, sf) = block(dag, sign, "module_signature")?;
    match (tag, sf) {
        // NoFunctor of structure_body
        (0, [struc]) => walk_structure(dag, *struc, prefix, out, depth),
        // MoreFunctor: a functor; its fields only make sense per-application.
        (1, _) => Ok(()),
        _ => Err(structure(
            "module_signature",
            format!("unexpected tag {tag}"),
        )),
    }
}

/// Walk a `structure_body = (Label.t * structure_field_body) list`.
fn walk_structure(
    dag: &MarshalDag,
    struc: MValue,
    prefix: &str,
    out: &mut VoLibraryContent,
    depth: usize,
) -> VoResult<()> {
    let entries = dag
        .list(struc)
        .ok_or_else(|| structure("structure_body", "expected list"))?;
    for entry in entries {
        let ef = tuple(dag, entry, 2, "structure entry")?;
        let label = string(dag, ef[0], "structure label")?;
        let qualified = format!("{prefix}.{label}");
        let (tag, ff) = block(dag, ef[1], "structure_field_body")?;
        match (tag, ff) {
            // SFBconst of constant_body
            (0, [cb]) => out
                .constants
                .push(read_constant(dag, *cb, label, qualified)?),
            // SFBmind of mutual_inductive_body
            (1, [mib]) => out
                .inductives
                .push(read_inductive(dag, *mib, label, qualified)?),
            // SFBrules of rewrite_rules_body — no declarations to extract.
            (2, _) => {}
            // SFBmodule of module_body
            (3, [sub]) => {
                out.modules.push(qualified.clone());
                walk_module(dag, *sub, &qualified, out, depth + 1)?;
            }
            // SFBmodtype of module_type_body — a specification, not
            // declarations; record the name only.
            (4, _) => out.modules.push(qualified),
            _ => {
                return Err(structure(
                    "structure_field_body",
                    format!("unexpected tag {tag} for {qualified}"),
                ))
            }
        }
    }
    Ok(())
}

/// Read a `constant_body` (9 fields, `checker/values.ml:v_cb`).
fn read_constant(
    dag: &MarshalDag,
    cb: MValue,
    label: String,
    qualified: String,
) -> VoResult<VoConstant> {
    let f = tuple(dag, cb, 9, "constant_body")?;
    let type_val = f[3];
    let (def_tag, def_fields) = block(dag, f[2], "constant_def")?;
    let (def, body_val, opaque_index) = match (def_tag, def_fields) {
        (0, _) => (ConstantDefKind::Undef, None, None),
        (1, [body]) => (ConstantDefKind::Def, Some(*body), None),
        (2, [opaque]) => {
            // opaque = (substs, cooking, dirpath, table index)
            let of = tuple(dag, *opaque, 4, "Opaqueproof.opaque")?;
            let idx = dag
                .int(of[3])
                .ok_or_else(|| structure("opaque index", "expected int"))?;
            (ConstantDefKind::OpaqueDef, None, Some(idx))
        }
        (3, _) => (ConstantDefKind::Primitive, None, None),
        (4, _) => (ConstantDefKind::Symbol, None, None),
        _ => {
            return Err(structure(
                "constant_def",
                format!("unexpected tag {def_tag} for {qualified}"),
            ))
        }
    };
    Ok(VoConstant {
        label,
        qualified,
        def,
        type_val,
        body_val,
        opaque_index,
    })
}

/// Read a `mutual_inductive_body` (15 fields, `checker/values.ml:v_ind_pack`).
fn read_inductive(
    dag: &MarshalDag,
    mib: MValue,
    label: String,
    qualified: String,
) -> VoResult<VoInductiveBlock> {
    let f = tuple(dag, mib, 15, "mutual_inductive_body")?;
    let packets = dag
        .array(f[0])
        .ok_or_else(|| structure("mind_packets", "expected array"))?;
    let mut type_names = Vec::with_capacity(packets.len());
    let mut ctor_names = Vec::with_capacity(packets.len());
    let mut ctor_type_vals = Vec::with_capacity(packets.len());
    for p in packets {
        // one_inductive_body (16 fields): [0]=mind_typename,
        // [3]=mind_consnames, [4]=mind_user_lc.
        let pf = tuple(dag, *p, 16, "one_inductive_body")?;
        type_names.push(string(dag, pf[0], "mind_typename")?);
        let cons = dag
            .array(pf[3])
            .ok_or_else(|| structure("mind_consnames", "expected array"))?;
        ctor_names.push(
            cons.iter()
                .map(|c| string(dag, *c, "mind_consname"))
                .collect::<VoResult<_>>()?,
        );
        let lc = dag
            .array(pf[4])
            .ok_or_else(|| structure("mind_user_lc", "expected array"))?;
        ctor_type_vals.push(lc.to_vec());
    }
    Ok(VoInductiveBlock {
        label,
        qualified,
        type_names,
        ctor_names,
        ctor_type_vals,
    })
}

// ---------------------------------------------------------------------------
// Opaques segment
// ---------------------------------------------------------------------------

/// Look up a proof term in the `opaques` segment table
/// (`opaque_disk = (Constr.t * delayed_universes) option array`).
///
/// Returns the `Constr` handle for the proof body, or `None` if the slot is
/// empty (proof pruned with `-vos`-style workflows).
///
/// # Errors
///
/// Returns `VoParseError::Structure` if the segment is not an opaque table
/// or the index is out of range.
pub fn read_opaque_proof(dag: &MarshalDag, index: i64) -> VoResult<Option<MValue>> {
    let table = dag
        .array(dag.root)
        .ok_or_else(|| structure("opaque_disk", "expected array"))?;
    let idx = usize::try_from(index)
        .map_err(|_| structure("opaque_disk", format!("negative index {index}")))?;
    let slot = table
        .get(idx)
        .ok_or_else(|| structure("opaque_disk", format!("index {index} out of range")))?;
    match dag
        .opt(*slot)
        .ok_or_else(|| structure("opaque_disk slot", "expected option"))?
    {
        None => Ok(None),
        Some(pair) => {
            let pf = tuple(dag, pair, 2, "opaque_proofterm")?;
            Ok(Some(pf[0]))
        }
    }
}
