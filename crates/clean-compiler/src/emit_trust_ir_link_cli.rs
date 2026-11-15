// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The CLI-facing half of the import producer (WS6.8): what `clean compile
//! --emit trustir-bin --link-artifact <PATH>` (clean-cli `cmd_compile`) calls.
//! Decoding an artifact ([`LinkedArtifact::decode`]), the table that decides
//! which symbols the client imports rather than defines
//! ([`importable_symbols`]), and the entry point
//! ([`link_imported_modules_for_cli`]) that runs the parent module's producer
//! and ends with the consumer's own check.

use super::*;

/// The consumer's verdict over `client` with `deps` as the supplied closure:
/// `validate_linked_module` under `RejectingModuleProofAuthority` — the call
/// `trust-ir validate --link <client> <deps..>` makes, and the one
/// [`link_imported_modules`] ends with. Empty means every row was re-earned;
/// otherwise one rendered `ValidationError` per refusal, by name.
#[must_use]
pub fn linked_verdict(client: &Module, deps: &[Module]) -> Vec<String> {
    let set = ModuleSet::new(deps.iter());
    validate_linked_module(client, &set, &RejectingModuleProofAuthority)
        .errors()
        .iter()
        .map(|e| format!("{e:?}"))
        .collect()
}

/// A dependency artifact the invoker named, already DECODED.
///
/// Decoding goes through the canonical reader
/// (`trust_ir::binary::deserialize_module`, via [`LinkedArtifact::decode`]),
/// so an unknown tag or a trailing byte refuses at load rather than here.
/// `path` is carried for diagnostics ONLY — identity is the digest computed
/// from `module`.
#[derive(Debug, Clone)]
pub struct LinkedArtifact {
    /// Where the bytes came from. Diagnostics only; never identity.
    pub path: String,
    /// The decoded dependency module.
    pub module: Module,
}

impl LinkedArtifact {
    /// Decode an artifact's bytes through the canonical reader.
    ///
    /// Only PLAIN module bytes are accepted (`clean compile --emit
    /// trustir-bin`). A `.tmbc` container (`b"tMBC"` + a little-endian `u32`
    /// ahead of the module, what `--emit obj` hands trust-cg) is refused by
    /// name: `Module::stable_digest` is computed over the MODULE, so an import
    /// row recorded from a container would name bytes the file does not hold.
    /// Any other decode failure (unknown tag, trailing byte, a refused wire
    /// version) is the reader's own refusal, passed through.
    ///
    /// # Errors
    ///
    /// A message naming `path` and why the bytes are not a linkable module.
    pub fn decode(path: impl Into<String>, bytes: &[u8]) -> Result<Self, String> {
        let path = path.into();
        if bytes.starts_with(b"tMBC") {
            return Err(format!(
                "linked artifact {path}: a `.tmbc` container, not a trust-ir module; the \
                 import digest is taken over the MODULE, so link against the plain module \
                 bytes `clean compile --emit trustir-bin` writes"
            ));
        }
        let module = trust_ir::binary::deserialize_module(bytes)
            .map_err(|e| format!("linked artifact {path}: not a trust-ir module: {e}"))?;
        Ok(Self { path, module })
    }
}

/// One symbol the client wants to import, with the client's OWN elaboration
/// of it.
#[derive(Debug, Clone)]
pub(crate) struct WantedSymbol {
    /// The link-time symbol.
    pub symbol: String,
    /// The client environment's `ConstantInfo.value` for the symbol — the
    /// definition the CLIENT means by it. A proof row is written only when the
    /// far certificate's recorded comparand equals the comparand this yields
    /// (module docs, step 6). `None` writes identity rows only.
    pub client_source: Option<Expr>,
}

impl WantedSymbol {
    /// A symbol wanted with NO client source definition: the link writes its
    /// identity rows only, never a proof row
    /// ([`LinkRefusal::ClientSourceUnavailable`]).
    #[must_use]
    pub(crate) fn identity_only(symbol: impl Into<String>) -> Self {
        Self {
            symbol: symbol.into(),
            client_source: None,
        }
    }

    /// A symbol wanted with the client's own source definition.
    #[must_use]
    pub(crate) fn with_source(symbol: impl Into<String>, client_source: Expr) -> Self {
        Self {
            symbol: symbol.into(),
            client_source: Some(client_source),
        }
    }
}

/// How the client treats one link-time symbol, given the supplied artifacts:
/// decided by the SAME symbol match the import producer uses ([`locate`]), so
/// the compile and the link cannot disagree about which artifact defines
/// what. A symbol no artifact defines (absent, only declared, or not
/// externally visible) has no entry in [`importable_symbols`]: the client
/// compiles it, exactly as without `--link-artifact`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArtifactLookup {
    /// Exactly one supplied artifact DEFINES the symbol (a body, externally
    /// visible linkage) and no other function in any artifact carries it:
    /// import it at this FAR signature instead of compiling it.
    Import(FuncTy),
    /// The symbol is DEFINED by two or more functions across the supplied
    /// artifacts. Never resolved by picking one.
    Ambiguous,
}

/// Every link-time symbol a supplied artifact carries that the client must
/// NOT define itself: [`ArtifactLookup::Import`] with the far signature when
/// exactly one artifact defines it, [`ArtifactLookup::Ambiguous`] when two or
/// more functions DEFINE it (another artifact's body-less declaration of it is
/// that artifact's own import, not a second definer). The key is the backend's
/// link-time spelling (the
/// string `Function::name` carries in every artifact this backend writes;
/// [`link_symbol`] spells a kernel name the same way).
///
/// The `Import` rows are the emitter's import table
/// ([`crate::emit_trust_ir::TrustIrConfig::imported_callees`]). They cover the
/// backend's AUXILIARY functions as well as source constants: an imported
/// `addmul`'s boxed-entry version (`l_addmul___boxed`), a hoisted constant or
/// a synthesized arithmetic wrapper is still generated by the client's
/// pipeline, and without this table the client would DEFINE a second copy of
/// a symbol the artifact already defines — the re-embedding linking replaces,
/// and a duplicate definition at native link time. A row the client's slice
/// never produces is simply unused.
#[must_use]
pub fn importable_symbols(linked: &[LinkedArtifact]) -> BTreeMap<String, ArtifactLookup> {
    let mut out = BTreeMap::new();
    for artifact in linked {
        for f in &artifact.module.functions {
            if out.contains_key(&f.name) {
                continue;
            }
            let row = match locate(linked, &f.name) {
                Ok((which, far)) => linked[which]
                    .module
                    .func_types
                    .get(far.ty.as_usize())
                    .map(|ft| ArtifactLookup::Import(ft.clone())),
                // DEFINED twice: never resolved by picking one. (A declaration
                // elsewhere — an artifact's own import of the symbol — is not
                // a second definer; see `locate`.)
                Err(LinkRefusal::SymbolAmbiguous) => Some(ArtifactLookup::Ambiguous),
                // Only declared, or not externally visible: nothing to link
                // against, so the client compiles its own.
                Err(_) => None,
            };
            if let Some(row) = row {
                out.insert(f.name.clone(), row);
            }
        }
    }
    out
}

/// The link-time symbol the backend writes for the kernel name `name`.
#[must_use]
pub fn link_symbol(name: &clean_kernel::Name) -> String {
    crate::emit_trust_ir::names::wire_name(name)
}

/// `fn(P0, P1, ..) -> R` — a signature spelled for a diagnostic.
pub(crate) fn render_func_ty(ft: &FuncTy) -> String {
    let params: Vec<String> = ft.params.iter().map(ToString::to_string).collect();
    let returns: Vec<String> = ft.returns.iter().map(ToString::to_string).collect();
    format!(
        "fn({}{}) -> ({})",
        params.join(", "),
        if ft.is_vararg { ", ..." } else { "" },
        returns.join(", ")
    )
}

/// The `clean compile --emit trustir-bin --link-artifact` entry point (WS6.8):
/// [`link_imported_modules`] over the module the backend just emitted.
///
/// `wanted` is one `(symbol, client source)` pair per declaration the emitter
/// wrote from the import table, the source being the client environment's
/// own definition of a source constant (`None` for an auxiliary function,
/// which then gets identity rows at most). The emitter has already DECLARED
/// every imported callee at its far signature
/// ([`crate::emit_trust_ir::TrustIrConfig::imported_callees`]), so the
/// producer adopts those declarations rather than minting a second one. It
/// ends with the consumer's own check, `validate_linked_module`, so nothing is
/// written that a consumer would not re-earn.
///
/// Returns one printable line per import row and per wanted symbol (proof
/// inherited, or identity only and why).
///
/// # Errors
///
/// A rendered refusal, leaving `client` unchanged, when the client DEFINES an
/// externally visible symbol a linked artifact also defines, an artifact
/// cannot be recorded, the consumer's check refuses the result, or a wanted
/// symbol got
/// NO import row: the client's declaration would then name a symbol nothing
/// binds, so the module must not be written.
pub fn link_imported_modules_for_cli(
    client: &mut Module,
    linked: &[LinkedArtifact],
    wanted: &[(String, Option<Expr>)],
) -> Result<Vec<String>, String> {
    link_for_cli(client, linked, wanted, None)
}

/// Link using the environment the client's source definitions came from, so
/// class dictionaries resolve from their checked values rather than names.
pub fn link_imported_modules_for_cli_in_environment(
    client: &mut Module,
    linked: &[LinkedArtifact],
    wanted: &[(String, Option<Expr>)],
    environment: &clean_kernel::Environment,
) -> Result<Vec<String>, String> {
    link_for_cli(client, linked, wanted, Some(environment))
}

fn link_for_cli(
    client: &mut Module,
    linked: &[LinkedArtifact],
    wanted: &[(String, Option<Expr>)],
    environment: Option<&clean_kernel::Environment>,
) -> Result<Vec<String>, String> {
    let wanted: Vec<WantedSymbol> = wanted
        .iter()
        .map(|(symbol, client_source)| match client_source {
            Some(source) => WantedSymbol::with_source(symbol.clone(), source.clone()),
            None => WantedSymbol::identity_only(symbol.clone()),
        })
        .collect();
    // A link-time symbol is DEFINED once. The emitter declares every symbol
    // an artifact defines (its import table is `importable_symbols`), so a
    // client definition of one is a path that bypassed that table — and a
    // duplicate definition at native link time, which no import row can make
    // sound. Refused by name rather than trusted to the emitter (WS6.8
    // review).
    let table = importable_symbols(linked);
    if let Some(f) = client.functions.iter().find(|f| {
        !f.is_declaration() && externally_visible(f.linkage) && table.contains_key(&f.name)
    }) {
        return Err(format!(
            "the client DEFINES `{}`, which a linked artifact already defines: two \
             definitions of one link-time symbol",
            f.name
        ));
    }
    let mut scratch = client.clone();
    let report = link_imported_modules_with_environment(&mut scratch, linked, &wanted, environment)
        .map_err(|e| e.to_string())?;
    if let Some((symbol, why)) = report.declined.first() {
        return Err(format!(
            "imported symbol `{symbol}` got no import row ({why})"
        ));
    }
    *client = scratch;
    let mut lines = Vec::new();
    for (id, name, digest) in &report.imports {
        lines.push(format!(
            "import #{} {name:?} stable digest {digest}",
            id.index()
        ));
    }
    for symbol in &report.proved {
        lines.push(format!("imported {} (proof inherited)", symbol.symbol));
    }
    for (symbol, why) in &report.identity_only {
        lines.push(format!("imported {} (identity only: {why})", symbol.symbol));
    }
    Ok(lines)
}
