// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lossless JSON transport of native bundles with shared replay formulas.
//! Decoding restores content only; it grants no live source or proof authority.

use super::NativeVerificationBundle;
use std::collections::{BTreeMap, BTreeSet};

/// Transport encoding of the `bundle`-role materialization's payload: the bundle's
/// own serde JSON, except that a request replay atom whose `formula` is
/// byte-for-byte the formula of the module proof obligation it names carries
/// `"formula_ref": {"obligation": <id>}` in its place.
///
/// Trust (G3, 2026-10-27): `native_replay_context` gives every request one replay
/// atom per obligation holding a clone of that obligation's formula, so the
/// bundle carried each formula twice. agy-alab's 12-line `civil_from_days`
/// (81 obligations, ~11.6 KB of predicate each) serialized to 19,736,563 bytes:
/// over `MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES` (16 MiB), so the bundle had
/// no inline materialization and every row of the function lost its native
/// evidence. All 81 atoms were byte-identical to their obligation's formula.
/// The cap is kept; the duplicate is not.
///
/// The encoding is lossless and self-describing. The payload is wrapped as
/// `{"encoding": <this>, "bundle": …}`, so no reader of the plain
/// `NativeVerificationBundle` JSON can mistake it for one (the bundle declares
/// `unknown_fields: Reject`, and the wrapper has none of its required fields).
/// [`rehydrate_native_bundle_transport_payload`] restores the exact typed bundle
/// and refuses a reference that is dangling, ambiguous, disagrees with its atom's
/// `obligation`, or whose restored formula does not reproduce the atom's recorded
/// `payload_digest`. Only the transport bytes change: the typed bundle every
/// engine consumes, its stable digests, and the per-request and per-obligation
/// artifacts (which still carry their atoms inline) are untouched.
pub const NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING: &str =
    "trust.native-bundle.replay-formula-ref.v1";

const REPLAY_FORMULA_REF_KEY: &str = "formula_ref";

/// The `bundle`-role payload in the [`NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING`].
/// Encoding content does not validate the bundle or grant source/proof authority.
///
/// # Errors
/// Returns an error if the typed bundle cannot be represented as JSON.
pub fn native_bundle_transport_payload(
    bundle: &NativeVerificationBundle,
) -> Result<serde_json::Value, String> {
    let mut value = serde_json::to_value(bundle).map_err(|error| {
        format!("typed TrustIr native transport JSON serialization failed: {error}")
    })?;
    let formulas = unique_obligation_formulas(&value).unwrap_or_default();
    for_each_replay_atom_mut(&mut value, |atom| {
        let Some(obligation) = atom.get("obligation").and_then(serde_json::Value::as_u64) else {
            return Ok(());
        };
        let Some(expected) = formulas.get(&obligation) else {
            return Ok(());
        };
        if atom.get("formula") == Some(expected) && !atom.contains_key(REPLAY_FORMULA_REF_KEY) {
            atom.remove("formula");
            atom.insert(
                REPLAY_FORMULA_REF_KEY.to_string(),
                serde_json::json!({ "obligation": obligation }),
            );
        }
        Ok(())
    })?;
    Ok(serde_json::json!({
        "encoding": NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING,
        "bundle": value,
    }))
}

/// Restore the typed bundle from a `bundle`-role payload written by
/// [`native_bundle_transport_payload`]: the reader for anyone who decodes a
/// `bundle`-role materialization (`{"encoding", "bundle"}` is its whole payload).
/// Fail-closed on every malformed shape.
///
/// # Errors
/// A payload in another encoding, a dangling, ambiguous or mismatched formula
/// reference, a bundle that does not decode, or a restored formula that does not
/// reproduce its atom's recorded `payload_digest`, or any fields that do not
/// survive exact re-encoding of the restored typed bundle's rehydrated JSON.
pub fn rehydrate_native_bundle_transport_payload(
    payload: &serde_json::Value,
) -> Result<NativeVerificationBundle, String> {
    let object = payload
        .as_object()
        .ok_or("native bundle transport payload is not an object")?;
    if object.len() != 2
        || object.get("encoding").and_then(serde_json::Value::as_str)
            != Some(NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING)
    {
        return Err(format!(
            "native bundle transport payload is not in the `{NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING}` encoding"
        ));
    }
    let mut value = object
        .get("bundle")
        .cloned()
        .ok_or("native bundle transport payload has no bundle")?;
    let formulas = unique_obligation_formulas(&value)?;
    let mut referenced = Vec::new();
    for_each_replay_atom_mut(&mut value, |atom| {
        let Some(reference) = atom.remove(REPLAY_FORMULA_REF_KEY) else {
            return Ok(());
        };
        if atom.contains_key("formula") {
            return Err(
                "replay atom carries both an inline formula and a formula reference".into(),
            );
        }
        let target = reference
            .as_object()
            .filter(|reference| reference.len() == 1)
            .and_then(|reference| reference.get("obligation"))
            .and_then(serde_json::Value::as_u64)
            .ok_or("replay atom formula reference is not `{\"obligation\": <id>}`")?;
        if atom.get("obligation").and_then(serde_json::Value::as_u64) != Some(target) {
            return Err(format!(
                "replay atom formula reference names obligation {target}, not the atom's own obligation"
            ));
        }
        let formula = formulas.get(&target).ok_or_else(|| {
            format!("replay atom formula reference names absent obligation {target}")
        })?;
        atom.insert("formula".to_string(), formula.clone());
        referenced.push(target);
        Ok(())
    })?;
    let bundle: NativeVerificationBundle = serde_json::from_value(value.clone())
        .map_err(|error| format!("native bundle transport payload does not decode: {error}"))?;
    // The reference is only as good as the digest it reproduces: the atom's recorded
    // `payload_digest` was computed over the formula the producer put there.
    for request in &bundle.requests {
        for atom in &request.provenance().replay_context.atoms {
            if atom
                .obligation
                .is_some_and(|id| referenced.contains(&u64::from(id.index())))
                && atom.payload_digest != atom.expected_payload_digest()
            {
                return Err(format!(
                    "rehydrated replay atom {} does not reproduce its recorded payload digest",
                    atom.id
                ));
            }
        }
    }
    // Consumers compare the restored typed request against independently bound
    // request/header artifacts. Do not let serde's ignored fields or defaults
    // erase a difference in that identity. Compare the rehydrated JSON, keeping
    // inline and reference encodings equally valid and ignoring object key order.
    // This checks content only, not admission or proof.
    let restored = serde_json::to_value(&bundle)
        .map_err(|error| format!("restored native bundle cannot be encoded: {error}"))?;
    if restored != value {
        return Err("native bundle transport loses fields during typed decoding".into());
    }
    Ok(bundle)
}

/// `module.proof_obligations[*].formula` by obligation id; `Err` when an id is
/// missing, not an integer, or repeated (a reference to it would be ambiguous).
fn unique_obligation_formulas(
    bundle: &serde_json::Value,
) -> Result<BTreeMap<u64, serde_json::Value>, String> {
    let mut formulas = BTreeMap::new();
    let mut ids = BTreeSet::new();
    let obligations = bundle
        .pointer("/module/proof_obligations")
        .and_then(serde_json::Value::as_array)
        .map(Vec::as_slice)
        .unwrap_or_default();
    for obligation in obligations {
        let id = obligation
            .get("id")
            .and_then(serde_json::Value::as_u64)
            .ok_or("module proof obligation has no integer id")?;
        // Identity is ambiguous even if one of the duplicate obligations has
        // no formula. Check every id before filtering formula-less rows.
        if !ids.insert(id) {
            return Err(format!("module proof obligation id {id} is repeated"));
        }
        let Some(formula) = obligation
            .get("formula")
            .filter(|formula| !formula.is_null())
        else {
            continue;
        };
        formulas.insert(id, formula.clone());
    }
    Ok(formulas)
}

/// Visit every `requests[*].<suite>.provenance.replay_context.atoms[*]` object.
fn for_each_replay_atom_mut(
    bundle: &mut serde_json::Value,
    mut visit: impl FnMut(&mut serde_json::Map<String, serde_json::Value>) -> Result<(), String>,
) -> Result<(), String> {
    let Some(requests) = bundle
        .get_mut("requests")
        .and_then(serde_json::Value::as_array_mut)
    else {
        return Ok(());
    };
    for request in requests {
        let Some(variants) = request.as_object_mut() else {
            continue;
        };
        for request in variants.values_mut() {
            let Some(atoms) = request
                .pointer_mut("/provenance/replay_context/atoms")
                .and_then(serde_json::Value::as_array_mut)
            else {
                continue;
            };
            for atom in atoms {
                if let Some(atom) = atom.as_object_mut() {
                    visit(atom)?;
                }
            }
        }
    }
    Ok(())
}
