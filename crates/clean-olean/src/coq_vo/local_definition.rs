// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::constr::{Constr, DirPath, ModPath};
use super::constr_decode::ConstrDecoder;
use super::library::{dirpath_dotted, read_summary, structure, tuple};
use super::marshal_parser::{MValue, MarshalDag};
use super::vo_parser::{VoObjFile, VoResult};

/// Where the original Coq object stores this definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionBody {
    Transparent,
    LocalQed,
}

/// Original decoded terms. A kernel must separately check their typing and dependencies.
#[derive(Debug)]
pub struct LocalDefinition<'a> {
    pub object: &'a [u8],
    pub library: String,
    pub qualified: String,
    pub kind: DefinitionBody,
    pub ty: Constr,
    pub body: Constr,
}

/// Read one named monomorphic definition from a Coq 8.20 object, including its
/// actual body. Resolve the library identity from the object and use its local
/// opaque table only for a Qed entry with no substitution or universe work.
/// A pruned body, axiom or functor cannot supply a term through this reader.
pub fn read_local_definition<'a>(
    bytes: &'a [u8],
    expected_library: &str,
    qualified: &str,
) -> VoResult<LocalDefinition<'a>> {
    let obj = VoObjFile::parse(bytes)?;
    if obj.version != 82000 {
        return Err(structure("local definition", "requires Coq 8.20"));
    }
    let summary = read_summary(&unique_segment(&obj, "summary")?)?;
    if summary.name != expected_library {
        return Err(structure("local definition", "unexpected original library"));
    }
    let dag = unique_segment(&obj, "library")?;
    let disk = tuple(&dag, dag.root, 3, "library_disk")?;
    let compiled = tuple(&dag, disk[0], 5, "compiled_library")?;
    if dirpath_dotted(&dag, compiled[0], "compiled library name")? != summary.name {
        return Err(structure(
            "local definition",
            "compiled and summary names differ",
        ));
    }
    let path = qualified
        .strip_prefix(expected_library)
        .and_then(|p| p.strip_prefix('.'))
        .ok_or_else(|| structure("local definition", "name outside selected library"))?;
    let root_path = ModPath::File(DirPath(
        expected_library
            .split('.')
            .rev()
            .map(str::to_owned)
            .collect(),
    ));
    let raw = select(&dag, compiled[1], root_path, path)?;
    let fields = tuple(&dag, raw, 9, "constant_body")?;
    let instance = tuple(&dag, fields[1], 2, "section instance")?;
    if dag.int(fields[0]) != Some(0)
        || dag.int(fields[6]) != Some(0)
        || !instance
            .iter()
            .all(|v| dag.array(*v).is_some_and(<[_]>::is_empty))
    {
        return Err(structure(
            "local definition",
            "requires a monomorphic definition outside sections",
        ));
    }
    let mut decoder = ConstrDecoder::new(&dag);
    let ty = decoder
        .constr(fields[3])
        .map_err(|e| structure("definition type", e.to_string()))?;
    let (kind, body) = match dag.block(fields[2]) {
        Some((1, [body])) => (
            DefinitionBody::Transparent,
            decoder
                .constr(*body)
                .map_err(|e| structure("transparent definition body", e.to_string()))?,
        ),
        Some((2, [handle])) => (
            DefinitionBody::LocalQed,
            local_opaque(&obj, &dag, *handle, &summary.name)?,
        ),
        _ => {
            return Err(structure(
                "local definition",
                "declaration has no regular definition body",
            ))
        }
    };
    Ok(LocalDefinition {
        object: bytes,
        library: summary.name,
        qualified: qualified.into(),
        kind,
        ty,
        body,
    })
}

fn unique_segment(obj: &VoObjFile<'_>, name: &str) -> VoResult<MarshalDag> {
    if obj.segments.iter().filter(|s| s.name == name).count() != 1 {
        return Err(structure(name, "expected one original segment"));
    }
    obj.read_segment(name)
}

fn select(
    dag: &MarshalDag,
    mut module: MValue,
    mut expected: ModPath,
    path: &str,
) -> VoResult<MValue> {
    let mut parts = path.split('.').peekable();
    while let Some(label) = parts.next() {
        if label.is_empty() {
            return Err(structure("local definition", "empty label"));
        }
        let fields = tuple(dag, module, 6, "module_body")?;
        let actual = ConstrDecoder::new(dag)
            .modpath(fields[0])
            .map_err(|e| structure("local definition module path", e.to_string()))?;
        if actual != expected || dag.int(fields[1]) != Some(1) {
            return Err(structure(
                "local definition",
                "requires an original full structure at its own module path",
            ));
        }
        let Some((0, [entries])) = dag.block(fields[2]) else {
            return Err(structure(
                "local definition",
                "requires a structure without functor parameters",
            ));
        };
        let entries = dag
            .list(*entries)
            .ok_or_else(|| structure("structure_body", "expected entry list"))?;
        let mut found = None;
        for entry in entries {
            let row = tuple(dag, entry, 2, "structure entry")?;
            if dag.string_lossy(row[0]).as_deref() != Some(label) {
                continue;
            }
            if found.is_some() {
                return Err(structure("local definition", "ambiguous structure label"));
            }
            found = Some(row[1]);
        }
        let field =
            found.ok_or_else(|| structure("local definition", format!("missing {label}")))?;
        match (parts.peek(), dag.block(field)) {
            (None, Some((0, [constant]))) => return Ok(*constant),
            (Some(_), Some((3, [nested]))) => {
                module = *nested;
                expected = ModPath::Dot(Box::new(expected), label.to_owned());
            }
            _ => {
                return Err(structure(
                    "local definition",
                    "unexpected structure field kind",
                ))
            }
        }
    }
    Err(structure("local definition", "empty name"))
}

fn local_opaque(
    obj: &VoObjFile<'_>,
    library: &MarshalDag,
    value: MValue,
    owner: &str,
) -> VoResult<Constr> {
    let handle = tuple(library, value, 4, "Opaqueproof.opaque")?;
    if library.int(handle[0]) != Some(0)
        || library.int(handle[1]) != Some(0)
        || dirpath_dotted(library, handle[2], "opaque proof library")? != owner
    {
        return Err(structure(
            "local Qed",
            "relocated proof or pending substitutions/cooking",
        ));
    }
    let index = library
        .int(handle[3])
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| structure("local Qed", "invalid opaque slot"))?;
    let dag = unique_segment(obj, "opaques")?;
    let slot = dag
        .array(dag.root)
        .and_then(|table| table.get(index))
        .and_then(|v| dag.opt(*v))
        .flatten()
        .ok_or_else(|| structure("local Qed", "missing opaque proof body"))?;
    let pair = tuple(&dag, slot, 2, "opaque_proofterm")?;
    if !matches!(dag.block(pair[1]), Some((0, [unit])) if dag.int(*unit) == Some(0)) {
        return Err(structure("local Qed", "unsupported delayed universes"));
    }
    ConstrDecoder::new(&dag)
        .constr(pair[0])
        .map_err(|e| structure("local Qed body", e.to_string()))
}
